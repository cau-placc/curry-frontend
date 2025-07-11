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
module Curry.Frontend.Interfaces (loadInterfaces) where

import           Prelude hiding ((<>))
import           Control.Monad               (unless)
import qualified Control.Monad.State    as S (StateT, execStateT, gets, modify)
import           Data.List.NonEmpty          (NonEmpty(..))
import qualified Data.Map               as M (insert, member)

import           Curry.Base.Ident
import           Curry.Base.Monad
import           Curry.Base.Position
import           Curry.Base.SpanInfo ()
import           Curry.Base.Pretty
import           Curry.Files.PathUtils
import           Curry.Syntax

import Curry.Frontend.Base.Messages
import Curry.Frontend.Env.Interface

import Curry.Frontend.Checks.InterfaceSyntaxCheck (intfSyntaxCheck)

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
loadInterface ctxt (_, m)
  | m `elem` ctxt = report [errCyclicImport $ m :| takeWhile (/= m) ctxt]
  | otherwise     = do
    isLoaded <- loaded m
    unless isLoaded $ do
      paths  <- searchPaths
      mbIntf <- liftIO $ lookupCurryInterface paths m
      case mbIntf of
        Nothing -> report [errInterfaceNotFound m]
        Just fn -> compileInterface ctxt m fn

-- |Compile an interface by recursively loading its dependencies.
--
-- After reading an interface, all imported interfaces are recursively
-- loaded and inserted into the interface's environment.
compileInterface :: [ModuleIdent] -> ModuleIdent -> FilePath
                 -> IntfLoader ()
compileInterface ctxt m fn = do
  mbSrc <- liftIO $ readModule fn
  case mbSrc of
    Nothing  -> report [errInterfaceNotFound m]
    Just src -> case runCYMIgnWarn (parseInterface fn src) of
      Left err -> report err
      Right intf@(Interface n is _ _) ->
        if m /= n
          then report [errWrongInterface m n]
          else do
            let (intf', intfErrs) = intfSyntaxCheck intf
            mapM_ report [intfErrs]
            mapM_ (loadInterface (m : ctxt)) [ (q, i) | IImportDecl q i _ <- is ]
            addInterface m intf'

-- Error message for required interface that could not be found.
errInterfaceNotFound :: ModuleIdent -> Message
errInterfaceNotFound m = spanInfoMessage m $
  text "Interface for module" <+> text (moduleName m) <+> text "not found"

-- Error message for an unexpected interface.
errWrongInterface :: ModuleIdent -> ModuleIdent -> Message
errWrongInterface m n = spanInfoMessage m $
  text "Expected interface for" <+> text (moduleName m)
  <> comma <+> text "but found" <+> text (moduleName n)

-- Error message for a cyclic import.
errCyclicImport :: NonEmpty ModuleIdent -> Message
errCyclicImport    (m :| []) = spanInfoMessage m $
  text "Recursive import for module" <+> text (moduleName m)
errCyclicImport ms@(m :| _)  = spanInfoMessage m $
  text "Cyclic import dependency between modules"
  <+> hsep (punctuate comma (map text inits)) <+> text "and" <+> text lastm
  where
  (inits, lastm)          = splitLast $ fmap moduleName ms
  splitLast (x :| [])     = ([]  , x)
  splitLast (x :| y : ys) = (x : xs, z) where (xs, z) = splitLast (y :| ys)
