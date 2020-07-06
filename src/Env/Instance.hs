{- |
    Module      :  $Header$
    Description :  Environment of instances
    Copyright   :  (c) 2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about defined instances in an
    environment that maps pairs of type classes and type constructors
    to the name of the module where the instance is declared, the context
    as given in the instance declaration, and a list of the class methods
    implemented in the specific instance along with their arity. A flat
    environment is sufficient because instances are visible globally and
    cannot be hidden. Instances are recorded only with the original names
    of the type class and type constructor involved.
-}

module Env.Instance
  ( InstIdent, ppInstIdent, InstInfo
  , InstEnv, initInstEnv, bindInstInfo, lookupInstInfo
  ) where

import qualified Data.Map as Map (Map, empty, insert, lookup)

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Syntax.Pretty

import Base.Types

type InstIdent = (QualIdent, QualIdent)

ppInstIdent :: InstIdent -> Doc
ppInstIdent (qcls, qtc) = ppQIdent qcls <+> ppQIdent qtc

type InstInfo = (ModuleIdent, PredSet, [(Ident, Int)])

type InstEnv = Map.Map InstIdent InstInfo

initInstEnv :: InstEnv
initInstEnv = Map.empty

bindInstInfo :: InstIdent -> InstInfo -> InstEnv -> InstEnv
bindInstInfo = Map.insert

lookupInstInfo :: InstIdent -> InstEnv -> Maybe InstInfo
lookupInstInfo = Map.lookup
