{- |
    Module      :  $Header$
    Description :  Checks extensions
    Copyright   :  (c)        2016 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   First of all, the compiler scans a source file for file-header pragmas
   that may activate language extensions.
-}
module Checks.ExtensionCheck (extensionCheck) where

import qualified Control.Monad.State as S (State, execState, modify)

import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.Messages (Message, posMessage)

import CompilerOpts

extensionCheck :: Options -> Module a -> ([KnownExtension], [Message])
extensionCheck opts mdl = execEXC (checkModule mdl) initState
  where
    initState = EXCState (optExtensions opts) []

type EXCM = S.State EXCState

data EXCState = EXCState
  { extensions :: [KnownExtension]
  , errors     :: [Message]
  }

execEXC :: EXCM a -> EXCState -> ([KnownExtension], [Message])
execEXC ecm s =
  let s' = S.execState ecm s in (extensions s', reverse $ errors s')

enableExtension :: KnownExtension -> EXCM ()
enableExtension e = S.modify $ \s -> s { extensions = e : extensions s }

report :: Message -> EXCM ()
report msg = S.modify $ \s -> s { errors = msg : errors s }

ok :: EXCM ()
ok = return ()

-- The extension check iterates over all given pragmas in the module and
-- gathers all extensions mentioned in a language pragma. An error is reported
-- if an extension is unknown.

checkModule :: Module a -> EXCM ()
checkModule (Module ps _ _ _ _) = mapM_ checkPragma ps

checkPragma :: ModulePragma -> EXCM ()
checkPragma (LanguagePragma _ exts) = mapM_ checkExtension exts
checkPragma (OptionsPragma  _  _ _) = ok

checkExtension :: Extension -> EXCM ()
checkExtension (KnownExtension   _ e) = enableExtension e
checkExtension (UnknownExtension p e) = report $ errUnknownExtension p e

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errUnknownExtension :: Position -> String -> Message
errUnknownExtension p e = posMessage p $
  text "Unknown language extension:" <+> text e
