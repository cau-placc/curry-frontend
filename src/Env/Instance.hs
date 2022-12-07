{- |
    Module      :  $Header$
    Description :  Environment of instances
    Copyright   :  (c) 2016 - 2020 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about defined instances in an
    environment that maps pairs of type classes and type constructors
    to the name of the module where the instance is declared, the context
    as given in the instance declaration, and a list of the class methods
    implemented in the specific instance along with their arity. A flat
    environment is sufficient because instances are visible globally and
    cannot be hidden. Instances are recorded only with the original names
    of the type class and type constructor involved. The context also uses
    original names and is already minimized.
-}

module Env.Instance
  ( InstIdent, ppInstIdent, InstInfo
  , InstEnv, initInstEnv, bindInstInfo, removeInstInfo, lookupInstInfo
  , instEnvToList
  ) where

import qualified Data.Map as Map ( Map, empty, insert, delete, lookup, union
                                 , singleton, insertWith, adjust, toList
                                 )

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Syntax.Pretty

import Base.CurryTypes
import Base.TypeSubst
import Base.Types

-- Taken from Leif-Erik Krueger
-- Instances are now identified by their class name and
-- the types of the class arguments
type InstIdent = (QualIdent, [Type])

-- taken from Leif-Erik Krueger
ppInstIdent :: InstIdent -> Doc
ppInstIdent (qcls, tys) = ppQIdent qcls <+> 
  hsep (map (pPrintPrec 2 . fromType identSupply) tys)

type InstInfo = (ModuleIdent, PredSet, [(Ident, Int)])

-- taken from Leif-Erik Krueger
type InstEnv = Map.Map QualIdent (Map.Map [Type] InstInfo)

initInstEnv :: InstEnv
initInstEnv = Map.empty

-- taken from Leif-Erik Krueger
bindInstInfo :: InstIdent -> InstInfo -> InstEnv -> InstEnv
bindInstInfo (qcls,tys) instInfo = 
  Map.insertWith Map.union qcls (Map.singleton tys instInfo)

-- taken from Leif-Erik Krueger
removeInstInfo  :: InstIdent -> InstEnv -> InstEnv
removeInstInfo (qcls, tys) = Map.adjust (Map.delete tys) qcls

-- taken from Leif-Erik Krueger
lookupInstInfo :: InstIdent -> InstEnv -> Maybe InstInfo
lookupInstInfo (qcls, tys) iEnv = do
  clsMap <- Map.lookup qcls iEnv
  res    <- Map.lookup tys clsMap
  return res

-- from Leif-Erik Krueger
instEnvToList :: InstEnv -> [(InstIdent, InstInfo)]
instEnvToList iEnv = [ ((qcls,tys), iInfo) | 
                        (qcls,qclsMap) <- Map.toList iEnv,
                        (tys,iInfo) <- Map.toList qclsMap ]

-------------------------------------------------------------------------------
--- Type Matching and Unification
-------------------------------------------------------------------------------


unifyTypes :: [Type] -> [Type] -> Maybe TypeSubst
unifyTypes = undefined

unifyType :: Type -> Type -> Maybe TypeSubst
unifyType = undefined