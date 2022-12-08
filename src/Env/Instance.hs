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
                                 , singleton, insertWith, adjust, toList, member
                                 )

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Syntax.Pretty

import Base.CurryTypes
import Base.Subst
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

-- from Leif-Erik Krueger

matchTypes :: [Type] -> [Type] -> Maybe TypeSubst
matchTypes tys1 tys2 = foldr (\(ty1,ty2) msubst -> 
    msubst >>= matchType ty1 ty2)  (Just idSubst) (zip tys1 tys2)

matchType :: Type -> Type -> TypeSubst -> Maybe TypeSubst
matchType (TypeVariable tv) ty sigma@(Subst _ substMap)
  | Map.member tv substMap = if substVar sigma tv == ty
                             then Just sigma
                             else Nothing
  | otherwise              = Just (bindSubst tv ty sigma) 
matchType (TypeConstructor tc1) (TypeConstructor tc2) sigma
  | tc1 == tc2 = Just sigma
matchType (TypeApply ty11 ty12) (TypeApply ty21 ty22) sigma = do
  sigma' <- matchType ty11 ty21 sigma
  matchType ty12 ty22 sigma'
matchType (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) sigma = do
  sigma' <- matchType ty11 ty21 sigma
  matchType ty21 ty22 sigma'
matchType _  _ _ = Nothing

unifyTypes :: [Type] -> [Type] -> Maybe TypeSubst
unifyTypes []         []         = Just idSubst
unifyTypes (ty1:tys1) (ty2:tys2) = do
  sigma1 <- unifyTypes tys1 tys2
  sigma2 <- unifyType ty1 ty2
  return (compose sigma2 sigma1)
unifyTypes _           _         = Nothing

unifyType :: Type -> Type -> Maybe TypeSubst
unifyType (TypeVariable tv1) (TypeVariable tv2) 
  | tv1 == tv2 = Just idSubst
  | otherwise  = Just $ singleSubst tv1 (TypeVariable tv2)
unifyType (TypeVariable tv) ty
  | tv `elem` typeVars ty = Nothing
  | otherwise             = Just $ singleSubst tv ty
unifyType ty (TypeVariable tv) 
  = unifyType (TypeVariable tv) ty
unifyType (TypeConstructor tc1) (TypeConstructor tc2) 
  | tc1 == tc2 = Just idSubst
unifyType (TypeArrow ty11 ty12) (TypeArrow ty21 ty22)
  = unifyTypes [ty11,ty12] [ty21,ty22]
unifyType (TypeApply ty11 ty12) (TypeApply ty21 ty22)
  = unifyTypes [ty11,ty12] [ty21,ty22]
unifyType _   _  = Nothing