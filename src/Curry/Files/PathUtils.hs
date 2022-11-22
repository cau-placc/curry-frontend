{- |
    Module      :  $Header$
    Description :  Utility functions for reading and writing files
    Copyright   :  (c) 1999 - 2003, Wolfgang Lux
                       2011 - 2014, Björn Peemöller (bjp@informatik.uni-kiel.de)
                       2017       , Finn Teegen (fte@informatik.uni-kiel.de)
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable
-}

{-# LANGUAGE CPP #-}

module Curry.Files.PathUtils
  ( -- * Retrieving curry files
    lookupCurryFile
  , lookupCurryModule
  , lookupCurryInterface
  , lookupFile

    -- * Reading and writing modules from files
  , getModuleModTime
  , writeModule
  , readModule
  , writeBinaryModule
  , addVersion
  , checkVersion
  ) where

import qualified Control.Exception    as C (IOException, handle)
import           Data.List                 (isPrefixOf, isSuffixOf)
import qualified Data.ByteString.Lazy as B (ByteString, writeFile)
import           System.FilePath
import           System.Directory
import           System.IO

#if MIN_VERSION_directory(1,2,0)
import Data.Time                        (UTCTime)
#else
import System.Time                      (ClockTime)
#endif

import Curry.Base.Ident
import Curry.Files.Filenames

-- ---------------------------------------------------------------------------
-- Searching for files
-- ---------------------------------------------------------------------------

-- |Search in the given list of paths for the given 'FilePath' and eventually
-- return the file name of the found file.
--
-- - If the file name already contains a directory, then the paths to search
--   in are ignored.
-- - If the file name has no extension, then a source file extension is
--   assumed.
lookupCurryFile :: [FilePath] -> FilePath -> IO (Maybe FilePath)
lookupCurryFile paths fn = lookupFile paths exts fn
  where
  exts  | null fnExt = sourceExts
        | otherwise  = [fnExt]
  fnExt              = takeExtension fn

-- |Search for a given curry module in the given source file and
-- library paths. Note that the current directory is always searched first.
-- Returns the path of the found file.
lookupCurryModule :: [FilePath]          -- ^ list of paths to source files
                  -> [FilePath]          -- ^ list of paths to library files
                  -> ModuleIdent         -- ^ module identifier
                  -> IO (Maybe FilePath)
lookupCurryModule paths libPaths m =
  lookupFile (paths ++ libPaths) moduleExts (moduleNameToFile m)

-- |Search for an interface file in the import search path using the
-- interface extension 'icurryExt'. Note that the current directory is
-- always searched first.
lookupCurryInterface :: [FilePath]          -- ^ list of paths to search in
                     -> ModuleIdent         -- ^ module identifier
                     -> IO (Maybe FilePath) -- ^ the file path if found
lookupCurryInterface paths m = lookupFile paths [icurryExt] (moduleNameToFile m)

-- |Search in the given directories for the file with the specified file
-- extensions and eventually return the 'FilePath' of the file.
lookupFile :: [FilePath]          -- ^ Directories to search in
           -> [String]            -- ^ Accepted file extensions
           -> FilePath            -- ^ Initial file name
           -> IO (Maybe FilePath) -- ^ 'FilePath' of the file if found
lookupFile paths exts file = lookup' files
  where
  files     = [ normalise (p </> f) | p <- paths, f <- baseNames ]
  baseNames = map (replaceExtension file) exts

  lookup' []       = return Nothing
  lookup' (f : fs) = do
    exists <- doesFileExist f
    if exists then return (Just f) else lookup' fs

-- ---------------------------------------------------------------------------
-- Reading and writing files
-- ---------------------------------------------------------------------------

-- | Write the content to a file in the given directory.
writeModule :: FilePath -- ^ original path
            -> String   -- ^ file content
            -> IO ()
writeModule fn contents = do
  createDirectoryIfMissing True $ takeDirectory fn
  tryWriteFile fn contents

-- | Write the content in binary to a file in the given directory.
writeBinaryModule :: FilePath -- ^ original path
                  -> B.ByteString   -- ^ file content
                  -> IO ()
writeBinaryModule fn contents = do
  createDirectoryIfMissing True $ takeDirectory fn
  tryWriteBinaryFile (fn ++ "-bin") contents

-- | Read the specified module and returns either 'Just String' if
-- reading was successful or 'Nothing' otherwise.
readModule :: FilePath -> IO (Maybe String)
readModule = tryOnExistingFile readFileUTF8
 where
  readFileUTF8 :: FilePath -> IO String
  readFileUTF8 fn = do
    hdl <- openFile fn ReadMode
    hSetEncoding hdl utf8
    hGetContents hdl

-- | Get the modification time of a file, if existent
#if MIN_VERSION_directory(1,2,0)
getModuleModTime :: FilePath -> IO (Maybe UTCTime)
#else
getModuleModTime :: FilePath -> IO (Maybe ClockTime)
#endif
getModuleModTime = tryOnExistingFile getModificationTime

-- |Add the given version string to the file content
addVersion :: String -> String -> String
addVersion v content = "{- " ++ v ++ " -}\n" ++ content

-- |Check a source file for the given version string
checkVersion :: String -> String -> Either String String
checkVersion expected src = case lines src of
  [] -> Left "empty file"
  (l:ls) -> case getVersion l of
    Just v | v == expected -> Right (unlines ls)
           | otherwise     -> Left $ "Expected version `" ++ expected
                                     ++ "', but found version `" ++ v ++ "'"
    _                      -> Left $ "No version found"

  where
    getVersion s | "{- " `isPrefixOf` s && " -}" `isSuffixOf` s
                 = Just (reverse $ drop 3 $ reverse $ drop 3 s)
                 | otherwise
                 = Nothing

-- ---------------------------------------------------------------------------
-- Helper functions
-- ---------------------------------------------------------------------------

tryOnExistingFile :: (FilePath -> IO a) -> FilePath -> IO (Maybe a)
tryOnExistingFile action fn = C.handle ignoreIOException $ do
  exists <- doesFileExist fn
  if exists then Just <$> action fn
            else return Nothing

ignoreIOException :: C.IOException -> IO (Maybe a)
ignoreIOException _ = return Nothing

-- | Try to write a file. If it already exists and is not writable,
-- a warning is issued. This solves some file dependency problems
-- in global installations.
tryWriteFile :: FilePath -- ^ original path
             -> String   -- ^ file content
             -> IO ()
tryWriteFile fn contents = do
  exists <- doesFileExist fn
  if exists then C.handle issueWarning (writeFileUTF8 fn contents)
            else writeFileUTF8 fn contents
 where
  issueWarning :: C.IOException -> IO ()
  issueWarning _ = do
    putStrLn $ "*** Warning: cannot update file `" ++ fn ++ "' (update ignored)"
    return ()
  writeFileUTF8 :: FilePath -> String -> IO ()
  writeFileUTF8 fn' str =
    withFile fn' WriteMode (\hdl -> hSetEncoding hdl utf8 >> hPutStr hdl str)

-- | Try to write a file. If it already exists and is not writable,
-- a warning is issued. This solves some file dependency problems
-- in global installations.
tryWriteBinaryFile :: FilePath -- ^ original path
                   -> B.ByteString   -- ^ file content
                   -> IO ()
tryWriteBinaryFile fn contents = do
  exists <- doesFileExist fn
  if exists then C.handle issueWarning (B.writeFile fn contents)
            else B.writeFile fn contents
 where
  issueWarning :: C.IOException -> IO ()
  issueWarning _ = do
    putStrLn $ "*** Warning: cannot update file `" ++ fn ++ "' (update ignored)"
    return ()
