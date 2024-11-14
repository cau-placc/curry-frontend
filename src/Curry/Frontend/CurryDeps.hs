{- |
    Module      :  $Header$
    Description :  Computation of module dependencies
    Copyright   :  (c) 2002 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2007        Sebastian Fischer
                       2011 - 2013 Björn Peemöller
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements the functions to compute the dependency
    information between Curry modules. This is used to create Makefile
    dependencies and to update programs composed of multiple modules.
-}
module CurryDeps
  ( Source (..), flatDeps, deps, flattenDeps, sourceDeps, moduleDeps ) where

import           Prelude hiding ((<>))
import           Control.Monad   (foldM)
import           Data.List       (isSuffixOf, nub)
import qualified Data.Map as Map (Map, empty, insert, lookup, toList)

import Curry.Base.Ident
import Curry.Base.Monad
import Curry.Base.Pretty
import Curry.Files.Filenames
import Curry.Files.PathUtils
import Curry.Syntax
  ( Module (..), ModulePragma (..), ImportDecl (..), parseHeader, parsePragmas
  , patchModuleId, hasLanguageExtension)

import Base.Messages
import Base.SCC (scc)
import CompilerOpts (Options (..), CppOpts (..), KnownExtension (..))
import CondCompile (condCompile)

-- |Different types of source files
data Source
    -- | A source file with pragmas and module imports
  = Source FilePath [ModulePragma] [ModuleIdent]
    -- | An interface file
  | Interface FilePath
    -- | An unknown file
  | Unknown
    deriving (Eq, Show)

type SourceEnv = Map.Map ModuleIdent Source

-- |Retrieve the dependencies of a source file in topological order
-- and possible errors during flattering
flatDeps :: Options -> FilePath -> CYIO [(ModuleIdent, Source)]
flatDeps opts fn = do
  sEnv <- deps opts Map.empty fn
  case flattenDeps sEnv of
    (env, []  ) -> ok env
    (_  , errs) -> failMessages errs

-- |Retrieve the dependencies of a source file as a 'SourceEnv'
deps :: Options -> SourceEnv -> FilePath -> CYIO SourceEnv
deps opts sEnv fn
  | ext   ==   icurryExt  = return sEnv
  | ext `elem` sourceExts = sourceDeps opts sEnv fn
  | otherwise             = targetDeps opts sEnv fn
  where ext = takeExtension fn

-- The following functions are used to lookup files related to a given
-- module. Source files for targets are looked up in the current
-- directory only. Two different search paths are used to look up
-- imported modules, the first is used to find source modules, whereas
-- the library path is used only for finding matching interface files. As
-- the compiler does not distinguish these paths, we actually check for
-- interface files in the source paths as well.

-- In order to compute the dependency graph, source files for each module
-- need to be looked up. When a source module is found, its header is
-- parsed in order to determine the modules that it imports, and
-- dependencies for these modules are computed recursively. The prelude
-- is added implicitly to the list of imported modules except for the
-- prelude itself.

-- |Retrieve the dependencies of a given target file
targetDeps :: Options -> SourceEnv -> FilePath -> CYIO SourceEnv
targetDeps opts sEnv fn = do
  mFile <- liftIO $ lookupFile [""] sourceExts fn
  case mFile of
    Nothing   -> return $ Map.insert (mkMIdent [fn]) Unknown sEnv
    Just file -> sourceDeps opts sEnv file

-- |Retrieve the dependencies of a given source file
sourceDeps :: Options -> SourceEnv -> FilePath -> CYIO SourceEnv
sourceDeps opts sEnv fn = readHeader opts fn >>= moduleDeps opts sEnv fn

-- |Retrieve the dependencies of a given module
moduleDeps :: Options -> SourceEnv -> FilePath -> Module a -> CYIO SourceEnv
moduleDeps opts sEnv fn mdl@(Module _ _ ps m _ _ _) = case Map.lookup m sEnv of
  Just  _ -> return sEnv
  Nothing -> do
    let imps  = imports opts mdl
        sEnv' = Map.insert m (Source fn ps imps) sEnv
    foldM (moduleIdentDeps opts) sEnv' imps

-- |Retrieve the imported modules and add the import of the Prelude
-- according to the compiler options.
imports :: Options -> Module a -> [ModuleIdent]
imports opts mdl@(Module _ _ _ m _ is _) = nub $
     [preludeMIdent | m /= preludeMIdent && not noImplicitPrelude]
  ++ [m' | ImportDecl _ m' _ _ _ <- is]
  where noImplicitPrelude = NoImplicitPrelude `elem` optExtensions opts
                              || mdl `hasLanguageExtension` NoImplicitPrelude

-- |Retrieve the dependencies for a given 'ModuleIdent'
moduleIdentDeps :: Options -> SourceEnv -> ModuleIdent -> CYIO SourceEnv
moduleIdentDeps opts sEnv m = case Map.lookup m sEnv of
  Just _  -> return sEnv
  Nothing -> do
    mFile <- liftIO $ lookupCurryModule ("." : optImportPaths opts)
                                        (optLibraryPaths opts) m
    case mFile of
      Nothing -> return $ Map.insert m Unknown sEnv
      Just fn
        | icurryExt `isSuffixOf` fn ->
            return $ Map.insert m (Interface fn) sEnv
        | otherwise                 -> do
            hdr@(Module _ _ _ m' _ _ _) <- readHeader opts fn
            if m == m' then moduleDeps opts sEnv fn hdr
                       else failMessages [errWrongModule m m']

readHeader :: Options -> FilePath -> CYIO (Module ())
readHeader opts fn = do
  mbFile <- liftIO $ readModule fn
  case mbFile of
    Nothing  -> failMessages [errMissingFile fn]
    Just src -> do
      prgs <- liftCYM $ parsePragmas fn src
      let cppOpts  = optCppOpts opts
          cppOpts' =
            cppOpts { cppRun = cppRun cppOpts || hasLanguageExtension prgs CPP }
      condC <- condCompile cppOpts' fn src
      hdr <- liftCYM $ parseHeader fn condC
      return $ patchModuleId fn hdr

-- If we want to compile the program instead of generating Makefile
-- dependencies, the environment has to be sorted topologically. Note
-- that the dependency graph should not contain any cycles.
flattenDeps :: SourceEnv -> ([(ModuleIdent, Source)], [Message])
flattenDeps = fdeps . sortDeps
  where
  sortDeps :: SourceEnv -> [[(ModuleIdent, Source)]]
  sortDeps = scc idents imported . Map.toList

  idents (m, _) = [m]

  imported (_, Source _ _ ms) = ms
  imported (_,             _) = []

  isRecursiveImport :: (ModuleIdent, Source) -> Bool
  isRecursiveImport (m, Source _ _ imps) = m `elem` imps
  isRecursiveImport (_, _              ) = False

  fdeps :: [[(ModuleIdent, Source)]] -> ([(ModuleIdent, Source)], [Message])
  fdeps = foldr checkdep ([], [])

  checkdep []    (srcs, errs)                         = (srcs      , errs      )
  checkdep [src] (srcs, errs) | isRecursiveImport src = (srcs      , err : errs)
                              | otherwise             = (src : srcs, errs      )
    where err = errCyclicImport (idents src)
  checkdep dep   (srcs, errs)                         = (srcs      , err : errs)
    where err = errCyclicImport $ map fst dep

errMissingFile :: FilePath -> Message
errMissingFile fn = message $ sep $ map text [ "Missing file:", fn ]

errWrongModule :: ModuleIdent -> ModuleIdent -> Message
errWrongModule m m' = message $ sep $
  [ text "Expected module for", text (moduleName m) <> comma
  , text "but found", text (moduleName m') ]

errCyclicImport :: [ModuleIdent] -> Message
errCyclicImport []       = internalError "CurryDeps.errCyclicImport: empty list"
errCyclicImport [m]      = spanInfoMessage m $ sep $ map text
  [ "Recursive import for module", moduleName m ]
errCyclicImport ms@(m:_) = spanInfoMessage m $ sep $
  text "Cyclic import dependency between modules" : punctuate comma inits
  ++ [text "and", lastm]
  where
  (inits, lastm)     = splitLast $ map (text . moduleName) ms
  splitLast []       = internalError "CurryDeps.splitLast: empty list"
  splitLast (x : []) = ([]    , x)
  splitLast (x : xs) = (x : ys, y) where (ys, y) = splitLast xs
