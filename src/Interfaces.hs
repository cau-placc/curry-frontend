{- |
    Module      :  $Header$
    Description :  Loading interfaces
    Copyright   :  (c) 2000 - 2004, Wolfgang Lux
                       2011 - 2013, Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains a global environment holding all (directly or
    indirectly) imported interface declarations for a module.

    This module contains a function to load *all* interface declarations
    declared by the (directly or indirectly) imported modules, regardless
    whether they are included by the import specification or not.

    The declarations are later brought into the scope of the module via the
    function 'importModules', see module "Imports".

    Interface files are updated by the Curry builder when necessary,
    see module "CurryBuilder".
-}
{-# LANGUAGE CPP #-}
module Interfaces (loadInterfaces) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import           Control.Monad               (unless)
import qualified Control.Monad.State    as S (StateT, execStateT, gets, modify)
import qualified Data.Map               as M (insert, member)

import           Curry.Base.Ident
import           Curry.Base.Monad
import           Curry.Base.Position
import           Curry.Base.SpanInfo ()
import           Curry.Base.Pretty
import           Curry.Files.PathUtils
import           Curry.Syntax

import Base.Messages
import Env.Interface

import Checks.InterfaceSyntaxCheck (intfSyntaxCheck)

-- Interface accumulating monad
type IntfLoader a = S.StateT LoaderState IO a

data LoaderState = LoaderState
  { iEnv   :: InterfaceEnv
  , spaths :: [FilePath]
  , errs   :: [Message]
  }

-- Report an error.
report :: [Message] -> IntfLoader ()
report msg = S.modify $ \ s -> s { errs = msg ++ errs s }

-- Check whether a module interface is already loaded.
loaded :: ModuleIdent -> IntfLoader Bool
loaded m = S.gets $ \ s -> m `M.member` iEnv s

-- Retrieve the search paths
searchPaths :: IntfLoader [FilePath]
searchPaths = S.gets spaths

-- Add an interface to the environment.
addInterface :: ModuleIdent -> Interface -> IntfLoader ()
addInterface m intf = S.modify $ \ s -> s { iEnv = M.insert m intf $ iEnv s }

-- |Load the interfaces needed by a given module.
-- This function returns an 'InterfaceEnv' containing the 'Interface's which
-- were successfully loaded.
loadInterfaces :: [FilePath] -- ^ 'FilePath's to search in for interfaces
               -> Module a   -- ^ 'Module' header with import declarations
               -> CYIO InterfaceEnv
loadInterfaces paths (Module _ _ _ m _ is _) = do
  res <- liftIO $ S.execStateT load (LoaderState initInterfaceEnv paths [])
  if null (errs res) then ok (iEnv res) else failMessages (reverse $ errs res)
  where load = mapM_ (loadInterface [m]) [(p, m') | ImportDecl p m' _ _ _ <- is]

-- |Load an interface into the given environment.
--
-- If an import declaration for a module is found, the compiler first
-- checks whether an import for the module is already pending.
-- In this case the module imports are cyclic which is not allowed in Curry.
-- Therefore, the import will be skipped and an error will be issued.
-- Otherwise, the compiler checks whether the module has already been imported.
-- If so, nothing needs to be done, otherwise the interface will be searched
-- for in the import paths and compiled.
loadInterface :: HasPosition a => [ModuleIdent] -> (a, ModuleIdent)
              -> IntfLoader ()
loadInterface ctxt imp@(pp, m)
  | m `elem` ctxt = report [errCyclicImport p (m : takeWhile (/= m) ctxt)]
  | otherwise     = do
    isLoaded <- loaded m
    unless isLoaded $ do
      paths  <- searchPaths
      mbIntf <- liftIO $ lookupCurryInterface paths m
      case mbIntf of
        Nothing -> report [errInterfaceNotFound p m]
        Just fn -> compileInterface ctxt imp fn
  where p = getPosition pp

-- |Compile an interface by recursively loading its dependencies.
--
-- After reading an interface, all imported interfaces are recursively
-- loaded and inserted into the interface's environment.
compileInterface :: HasPosition p => [ModuleIdent] -> (p, ModuleIdent) -> FilePath
                 -> IntfLoader ()
compileInterface ctxt (p, m) fn = do
  mbSrc <- liftIO $ readModule fn
  case mbSrc of
    Nothing  -> report [errInterfaceNotFound p m]
    Just src -> case runCYMIgnWarn (parseInterface fn src) of
      Left err -> report err
      Right intf@(Interface n is _) ->
        if m /= n
          then report [errWrongInterface (first fn) m n]
          else do
            let (intf', intfErrs) = intfSyntaxCheck intf
            mapM_ report [intfErrs]
            mapM_ (loadInterface (m : ctxt)) [ (q, i) | IImportDecl q i <- is ]
            addInterface m intf'

-- Error message for required interface that could not be found.
errInterfaceNotFound :: HasPosition p => p -> ModuleIdent -> Message
errInterfaceNotFound p m = posMessage p $
  text "Interface for module" <+> text (moduleName m) <+> text "not found"

-- Error message for an unexpected interface.
errWrongInterface :: HasPosition p => p -> ModuleIdent -> ModuleIdent -> Message
errWrongInterface p m n = posMessage p $
  text "Expected interface for" <+> text (moduleName m)
  <> comma <+> text "but found" <+> text (moduleName n)

-- Error message for a cyclic import.
errCyclicImport :: HasPosition p => p -> [ModuleIdent] -> Message
errCyclicImport _ []  = internalError "Interfaces.errCyclicImport: empty list"
errCyclicImport p [m] = posMessage p $
  text "Recursive import for module" <+> text (moduleName m)
errCyclicImport p ms  = posMessage p $
  text "Cyclic import dependency between modules"
  <+> hsep (punctuate comma (map text inits)) <+> text "and" <+> text lastm
  where
  (inits, lastm)         = splitLast $ map moduleName ms
  splitLast []           = internalError "Interfaces.splitLast: empty list"
  splitLast (x : [])     = ([]  , x)
  splitLast (x : y : ys) = (x : xs, z) where (xs, z) = splitLast (y : ys)
