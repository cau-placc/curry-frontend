{- |
    Module      :  $Header$
    Description :  File names for several intermediate file formats.
    Copyright   :  (c) 2009        Holger Siegel
                       2013 - 2014 Björn Peemöller
                       2018        Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The functions in this module were collected from several compiler modules
    in order to provide a unique accessing point for this functionality.
-}
module Curry.Files.Filenames
  ( -- * Re-exports from 'System.FilePath'
    FilePath, takeBaseName, dropExtension, takeExtension, takeFileName

    -- * Conversion between 'ModuleIdent' and 'FilePath'
  , moduleNameToFile, fileNameToModule, splitModuleFileName, isCurryFilePath

    -- * Curry sub-directory
  , defaultOutDir, hasOutDir, addOutDir, addOutDirModule
  , ensureOutDir

    -- * File name extensions
    -- ** Curry files
  , curryExt, lcurryExt, icurryExt

    -- ** FlatCurry files
  , typedFlatExt, flatExt, flatIntExt

    -- ** AbstractCurry files
  , acyExt, uacyExt

    -- ** Source and object files
  , sourceRepExt, sourceExts, moduleExts

    -- * Functions for computing file names
  , interfName, typedFlatName, typeAnnFlatName, flatName, flatIntName
  , acyName, uacyName, sourceRepName, tokensName, commentsName
  , astName, shortASTName, htmlName
  ) where

import System.FilePath

import Curry.Base.Ident

-- -----------------------------------------------------------------------------
-- Conversion between ModuleIdent and FilePath
-- -----------------------------------------------------------------------------

-- |Create a 'FilePath' from a 'ModuleIdent' using the hierarchical module
-- system
moduleNameToFile :: ModuleIdent -> FilePath
moduleNameToFile = foldr1 (</>) . midQualifiers

-- |Extract the 'ModuleIdent' from a 'FilePath'
fileNameToModule :: FilePath -> ModuleIdent
fileNameToModule = mkMIdent . splitDirectories . dropExtension . dropDrive

-- |Split a 'FilePath' into a prefix directory part and those part that
-- corresponds to the 'ModuleIdent'. This is especially useful for
-- hierarchically module names.
splitModuleFileName :: ModuleIdent -> FilePath -> (FilePath, FilePath)
splitModuleFileName m fn = case midQualifiers m of
  [_] -> splitFileName fn
  ms  -> let (base, ext) = splitExtension fn
             dirs        = splitDirectories base
             (pre, suf)  = splitAt (length dirs - length ms) dirs
             path        = if null pre then ""
                                       else addTrailingPathSeparator (joinPath pre)
         in  (path, joinPath suf <.> ext)

-- |Checks whether a 'String' represents a 'FilePath' to a Curry module
isCurryFilePath :: String -> Bool
isCurryFilePath str =  isValid str
                    && takeExtension str `elem` ("" : moduleExts)

-- -----------------------------------------------------------------------------
-- Curry sub-directory
-- -----------------------------------------------------------------------------

-- |The standard hidden subdirectory for curry files
defaultOutDir :: String
defaultOutDir = ".curry"

-- |Does the given 'FilePath' contain the 'outDir'
-- as its last directory component?
hasOutDir :: String -> FilePath -> Bool
hasOutDir outDir f = not (null dirs) && last dirs == outDir
  where dirs = splitDirectories $ takeDirectory f

-- |Add the 'outDir' to the given 'FilePath' if the flag is 'True' and
-- the path does not already contain it, otherwise leave the path untouched.
addOutDir :: Bool -> String -> FilePath -> FilePath
addOutDir b outDir fn = if b then ensureOutDir outDir fn else fn

-- |Add the 'outDir' to the given 'FilePath' if the flag is 'True' and
-- the path does not already contain it, otherwise leave the path untouched.
addOutDirModule :: Bool -> String -> ModuleIdent -> FilePath -> FilePath
addOutDirModule b outDir m fn
  | b         = let (pre, file) = splitModuleFileName m fn
                in  ensureOutDir outDir pre </> file
  | otherwise = fn

-- | Ensure that the 'outDir' is the last component of the
-- directory structure of the given 'FilePath'. If the 'FilePath' already
-- contains the sub-directory, it remains unchanged.
ensureOutDir :: String   -- ^ the 'outDir'
             -> FilePath -- ^ original 'FilePath'
             -> FilePath -- ^ new 'FilePath'
ensureOutDir outDir fn = normalise $ addSub (splitDirectories d) </> f
  where
  (d, f) = splitFileName fn
  addSub dirs | null dirs           = outDir
              | last dirs == outDir = joinPath dirs
              | otherwise           = joinPath dirs </> outDir

-- -----------------------------------------------------------------------------
-- File name extensions
-- -----------------------------------------------------------------------------

-- |Filename extension for non-literate curry files
curryExt :: String
curryExt = ".curry"

-- |Filename extension for literate curry files
lcurryExt :: String
lcurryExt = ".lcurry"

-- |Filename extension for curry interface files
icurryExt :: String
icurryExt = ".icurry"

-- |Filename extension for curry source files.
--
-- /Note:/ The order of the extensions defines the order in which source files
-- should be searched for, i.e. given a module name @M@, the search order
-- should be the following:
--
-- 1. @M.curry@
-- 2. @M.lcurry@
--
sourceExts :: [String]
sourceExts = [curryExt, lcurryExt]

-- |Filename extension for curry module files
-- TODO: Is the order correct?
moduleExts :: [String]
moduleExts = sourceExts ++ [icurryExt]

-- |Filename extension for typed flat-curry files
typedFlatExt :: String
typedFlatExt = ".tfcy"

-- |Filename extension for type-annotated flat-curry files
typeAnnFlatExt :: String
typeAnnFlatExt = ".tafcy"

-- |Filename extension for flat-curry files
flatExt :: String
flatExt = ".fcy"

-- |Filename extension for extended-flat-curry interface files
flatIntExt :: String
flatIntExt = ".fint"

-- |Filename extension for abstract-curry files
acyExt :: String
acyExt = ".acy"

-- |Filename extension for untyped-abstract-curry files
uacyExt :: String
uacyExt = ".uacy"

-- |Filename extension for curry source representation files
sourceRepExt :: String
sourceRepExt = ".cy"

-- |Filename extension for token files
tokensExt :: String
tokensExt = ".tokens"

-- |Filename extension for comment token files
commentsExt :: String
commentsExt = ".cycom"

-- |Filename extension for AST files
astExt :: String
astExt = ".ast"

-- |Filename extension for shortened AST files
shortASTExt :: String
shortASTExt = ".sast"

-- ---------------------------------------------------------------------------
-- Computation of file names for a given source file
-- ---------------------------------------------------------------------------

-- |Compute the filename of the interface file for a source file
interfName :: FilePath -> FilePath
interfName = replaceExtensionWith icurryExt

-- |Compute the filename of the typed flat curry file for a source file
typedFlatName :: FilePath -> FilePath
typedFlatName = replaceExtensionWith typedFlatExt

-- |Compute the filename of the typed flat curry file for a source file
typeAnnFlatName :: FilePath -> FilePath
typeAnnFlatName = replaceExtensionWith typeAnnFlatExt

-- |Compute the filename of the flat curry file for a source file
flatName :: FilePath -> FilePath
flatName = replaceExtensionWith flatExt

-- |Compute the filename of the flat curry interface file for a source file
flatIntName :: FilePath -> FilePath
flatIntName = replaceExtensionWith flatIntExt

-- |Compute the filename of the abstract curry file for a source file
acyName :: FilePath -> FilePath
acyName = replaceExtensionWith acyExt

-- |Compute the filename of the untyped abstract curry file for a source file
uacyName :: FilePath -> FilePath
uacyName = replaceExtensionWith uacyExt

-- |Compute the filename of the source representation file for a source file
sourceRepName :: FilePath -> FilePath
sourceRepName = replaceExtensionWith sourceRepExt

-- |Compute the filename of the tokens file for a source file
tokensName :: FilePath -> FilePath
tokensName = replaceExtensionWith tokensExt

-- |Compute the filename of the comment tokens file for a source file
commentsName :: FilePath -> FilePath
commentsName = replaceExtensionWith commentsExt

-- |Compute the filename of the ast file for a source file
astName :: FilePath -> FilePath
astName = replaceExtensionWith astExt

-- |Compute the filename of the ast file for a source file
shortASTName :: FilePath -> FilePath
shortASTName = replaceExtensionWith shortASTExt

-- |Compute the filename of the HTML file for a source file
htmlName :: ModuleIdent -> String
htmlName m = moduleName m ++ "_curry.html"

-- |Replace a filename extension with a new extension
replaceExtensionWith :: String -> FilePath -> FilePath
replaceExtensionWith = flip replaceExtension
