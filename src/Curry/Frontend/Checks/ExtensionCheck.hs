{- |
    Module      :  $Header$
    Description :  Checks extensions
    Copyright   :  (c)        2016 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   First of all, the compiler scans a source file for file-header pragmas
   that may activate language extensions. The extension check then adds
   all, possibly transitively, implied extensions to the set of enabled
   extensions.
-}
module Curry.Frontend.Checks.ExtensionCheck (extensionCheck) where

import qualified Control.Monad.State as S (State, execState, modify, gets)
import qualified Data.Set as Set
import qualified Data.Set.Extra as Set

import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax

import Curry.Frontend.Base.Messages (Message, spanInfoMessage)

import Curry.Frontend.CompilerOpts

extensionCheck :: Options -> Module a -> ([KnownExtension], [Message])
extensionCheck opts mdl = execEXC (checkModule mdl >> applyImplicitExtensions) initState
  where
    initState = EXCState (Set.fromList $ optExtensions opts) []

type EXCM = S.State EXCState

data EXCState = EXCState
  { extensions :: Set.Set KnownExtension
  , errors     :: [Message]
  }

execEXC :: EXCM a -> EXCState -> ([KnownExtension], [Message])
execEXC ecm s =
  let s' = S.execState ecm s in (Set.toList $ extensions s', reverse $ errors s')

enableExtensions :: Set.Set KnownExtension -> EXCM ()
enableExtensions es = S.modify $ \s -> s { extensions = Set.union es $ extensions s }

disableExtensions :: Set.Set KnownExtension -> EXCM ()
disableExtensions es = S.modify $ \s -> s { extensions = Set.difference (extensions s) es }

report :: Message -> EXCM ()
report msg = S.modify $ \s -> s { errors = msg : errors s }

ok :: EXCM ()
ok = return ()

-- In the first phase, the extension check iterates over all given pragmas in the
-- module and gathers all extensions mentioned in a language pragma. An error is
-- reported if an extension is unknown.

checkModule :: Module a -> EXCM ()
checkModule (Module _ _ ps _ _ _ _) = mapM_ checkPragma ps

checkPragma :: ModulePragma -> EXCM ()
checkPragma (LanguagePragma _ exts) = mapM_ checkExtension exts
checkPragma (OptionsPragma  _  _ _) = ok

checkExtension :: Extension -> EXCM ()
checkExtension (KnownExtension   _ e) = enableExtensions $ Set.singleton e
checkExtension (UnknownExtension p e) = report $ errUnknownExtension p e

-- In the second phase, the extension check updates the set of extensions with
-- implicitly added and removed extensions.

applyImplicitExtensions :: EXCM ()
applyImplicitExtensions = do
  enableExtensions . impliedClosure =<< S.gets extensions
  disableExtensions . Set.concatMap removedExtensions =<< S.gets extensions

-- ---------------------------------------------------------------------------
-- Implied extensions
-- ---------------------------------------------------------------------------

-- |Extensions implied by the given extension.
impliedExtensions :: KnownExtension -> Set.Set KnownExtension
impliedExtensions NoImplicitPrelude      = Set.singleton NoDataDeriving
impliedExtensions FunctionalDependencies = Set.singleton MultiParamTypeClasses
impliedExtensions _                      = Set.empty

-- |Extensions removed by the given extension.
removedExtensions :: KnownExtension -> Set.Set KnownExtension
removedExtensions NoAnonFreeVars       = Set.singleton AnonFreeVars
removedExtensions NoFunctionalPatterns = Set.singleton FunctionalPatterns
removedExtensions _                    = Set.empty

-- |Extensions implied (possibly transitively) by the given extensions.
impliedClosure :: Set.Set KnownExtension -> Set.Set KnownExtension
impliedClosure exts | exts == exts' = exts
                    | otherwise     = impliedClosure exts'
  where exts' = Set.union exts $ Set.concatMap impliedExtensions exts

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errUnknownExtension :: SpanInfo -> String -> Message
errUnknownExtension p e = spanInfoMessage p $
  text "Unknown language extension:" <+> text e
