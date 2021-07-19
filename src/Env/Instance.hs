{- |
    Module      :  $Header$
    Description :  Environment of instances
    Copyright   :  (c) 2016 - 2020 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about defined instances in an environment
    that maps type class names to the instances defined for that class. These
    instances are stored by mapping lists of type expressions (the instance
    types) to the name of the module where the instance is declared, the context
    as given in the instance declaration, and a list of the class methods
    implemented in the specific instance along with their arity. A flat
    environment is sufficient because instances are visible globally and cannot
    be hidden. Instances are recorded with normalized and fully expanded types
    and only use the original names of the type class and type constructors
    involved. The context also uses original names and is already minimized.
-}

module Env.Instance
  ( InstIdent, ppInstIdent, InstInfo, InstMatchInfo
  , InstEnv, initInstEnv, bindInstInfo, removeInstInfo, instEnvList
  , lookupInstExact, lookupInstMatch
  ) where

import qualified Data.Map as Map ( Map, adjust, empty, delete, insertWith
                                 , lookup, member, singleton, toList, union )

import Control.Monad ((<=<))

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Syntax.Pretty

import Base.Subst
import Base.Types
import Base.TypeSubst

-- An 'InstIdent' uniquely identifies an instance by its class name and instance
-- types.
type InstIdent = (QualIdent, [Type])

ppInstIdent :: InstIdent -> Doc
ppInstIdent (qcls, tys) = ppQIdent qcls <+> hsep (map pPrint tys)

-- An 'InstInfo' contains all relevant information about an instance declaration
-- beyond its identifier. These are its module, the given instance context, and
-- the implemented methods with their arity.
type InstInfo = (ModuleIdent, PredSet, [(Ident, Int)])

-- An 'InstMatchInfo' is represents a successful result when searching for a
-- matching instance. In addition to the information of an 'InstInfo', it
-- contains the original instance types of the matching instance and a type
-- substitution mapping instance types to the the requested types.
type InstMatchInfo = (ModuleIdent, PredSet, [Type], [(Ident, Int)], TypeSubst)

type InstEnv = Map.Map QualIdent (Map.Map [Type] InstInfo)

initInstEnv :: InstEnv
initInstEnv = Map.empty

bindInstInfo :: InstIdent -> InstInfo -> InstEnv -> InstEnv
bindInstInfo (qcls, tys) instInfo =
  Map.insertWith Map.union qcls (Map.singleton tys instInfo)

-- Removes the instance identified by the given 'InstIdent' from the instance
-- environment. Note that no type matching is performed, so only the instance
-- with exactly the given instance types is removed.
removeInstInfo :: InstIdent -> InstEnv -> InstEnv
removeInstInfo (qcls, tys) = Map.adjust (Map.delete tys) qcls

-- Converts the instance environment from a map to a list. For easier usage, the
-- nesting of the instance environment map is removed, such that the returned
-- list represents a map where 'InstIdent's are mapped to 'InstInfo's.
instEnvList :: InstEnv -> [(InstIdent, InstInfo)]
instEnvList inEnv = [ ((qcls, tys), instInfo)
                    | (qcls, instMap) <- Map.toList inEnv
                    , (tys, instInfo) <- Map.toList instMap ]

-- Looks up the instance identified by the given 'InstIdent' in the instance
-- environment. Note that no type matching is performed, so only the instance
-- with exactly the given instance types is looked up.
lookupInstExact :: InstIdent -> InstEnv -> Maybe InstInfo
lookupInstExact (qcls, tys) = Map.lookup tys <=< Map.lookup qcls

-- Looks up all instances of the given class in the instance environment that
-- match the given types and returns them as 'InstMatchInfo's.
lookupInstMatch :: QualIdent -> [Type] -> InstEnv -> [InstMatchInfo]
lookupInstMatch qcls tys inEnv =
  case Map.lookup qcls inEnv of
    Nothing      -> []
    Just instMap ->
      [ (m, ps, itys, is, sigma) | (itys, (m, ps, is)) <- Map.toList instMap
                                 , Just sigma <- [matchInstTypes itys tys] ]

-- Tries to match the given instance types (first argument) with the given
-- requested types (second argument) and returns the respective type
-- substitution, if successful. Note that the number of instance and requested
-- types is not checked.
matchInstTypes :: [Type] -> [Type] -> Maybe TypeSubst
matchInstTypes itys tys =
  foldr (\(ity, ty) -> (matchType ity ty =<<)) (Just idSubst) (zip itys tys)

-- Tries to match the given instance type (first argument) with the given
-- requested type (second argument) by expanding the given type substitution,
-- if successful.
matchType :: Type -> Type -> TypeSubst -> Maybe TypeSubst
matchType (TypeVariable tv) ty = bindSubst' tv ty
 where
  -- Expands the given type substitution by binding the given type variable
  -- index to the given type. Returns 'Nothing', if this type variable index is
  -- already bound to a different type by the type substitution.
  bindSubst' :: Int -> Type -> TypeSubst -> Maybe TypeSubst
  bindSubst' tv' ty' sigma@(Subst _ sigmaMap)
    | Map.member tv' sigmaMap = if substVar sigma tv' == ty' then Just sigma
                                                             else Nothing
    | otherwise               = Just (bindSubst tv' ty' sigma)

matchType (TypeConstructor tc1) (TypeConstructor tc2) | tc1 == tc2 = Just
matchType (TypeApply ty11 ty12) (TypeApply ty21 ty22) = matchType ty12 ty22 <=<
  matchType ty11 ty21
matchType (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) = matchType ty12 ty22 <=<
  matchType ty11 ty21
matchType (TypeApply ty11 ty12) (TypeArrow ty21 ty22) = matchType ty12 ty22 <=<
  matchType ty11 (TypeApply (TypeConstructor qArrowId) ty21)
matchType (TypeArrow ty11 ty12) (TypeApply ty21 ty22) = matchType ty12 ty22 <=<
  matchType (TypeApply (TypeConstructor qArrowId) ty11) ty21

matchType (TypeForall _ ty1) (TypeForall _ ty2) = matchType ty1 ty2
matchType (TypeForall _ ty1) ty2                = matchType ty1 ty2
matchType ty1                (TypeForall _ ty2) = matchType ty1 ty2
matchType _                  _                  = const Nothing
