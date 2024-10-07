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
  , lookupInstExact, lookupInstMatch, typeDepsInstEnv
  ) where

import           Data.Function   (on)
import qualified Data.Map as Map ( Map, adjust, empty, delete, insertWith, keys
                                 , lookup, member, singleton, toList, union )

import Control.Monad ((<=<))

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Syntax.Pretty

import Base.Subst
import Base.Types
import Base.TypeSubst

import Env.Class

-- An 'InstIdent' uniquely identifies an instance by its class name and instance
-- types.
type InstIdent = (QualIdent, [Type])

ppInstIdent :: InstIdent -> Doc
ppInstIdent (qcls, tys) =
  ppQIdent qcls <+> hsep (map (pPrintPrec 2 . fromType identSupply) tys)

-- An 'InstInfo' contains all relevant information about an instance declaration
-- beyond its identifier. These are its module, the given instance context, and
-- the implemented methods with their arity.
type InstInfo = (ModuleIdent, PredList, [(Ident, Int)])

-- An 'InstMatchInfo' is represents a successful result when searching for a
-- matching instance. In addition to the information of an 'InstInfo', it
-- contains the original instance types of the matching instance and a type
-- substitution mapping instance types to the the requested types.
type InstMatchInfo = (ModuleIdent, PredList, [Type], [(Ident, Int)], TypeSubst)

-- taken from Leif-Erik Krueger
type InstLookupResult = ([InstMatchInfo], [InstMatchInfo])

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
-- taken from Leif-Erik Krueger
lookupInstMatch :: QualIdent -> [Type] -> InstEnv -> InstLookupResult
lookupInstMatch qcls tys inEnv =
  case fmap Map.toList (Map.lookup qcls inEnv) of
    Nothing       -> ([], [])
    Just instList ->
      ( [ (m, ps, itys, is, sigma) | (itys, (m, ps, is)) <- instList
                                   , Just sigma <- [matchInstTypes itys tys] ]
      , [ (m, ps', itys', is, sigma)
        | (itys, (m, ps, is)) <- instList
        -- 'TypeConstrained's, which are special type variables standing for
        -- Int or Float, are converted to regular type variables here. They are
        -- treated specially in 'defaultTypeConstrained' in the type check.
        , let tys' = map removeTypeConstrained tys
              rnTvs = map TypeVariable [maximum (-1 : typeVars tys') + 1 ..]
              PredTypes ps' itys' = expandAliasType rnTvs $ PredTypes ps itys
        , Just sigma <- [unifyTypeLists itys' tys'] ]
      )

typeDepsInstEnv :: QualIdent -> [Type] -> ClassEnv -> InstEnv -> [(Type, Type)]
typeDepsInstEnv qcls tys clsEnv inEnv = filter (uncurry (/=)) $ concat
  [ zip (getFunDepRhs funDep tys) (subst sigma (getFunDepRhs funDep itys))
  | itys <- maybe [] Map.keys (Map.lookup qcls inEnv)
  , funDep <- classFunDeps qcls clsEnv
  , Just sigma <- [(matchInstTypes `on` getFunDepLhs funDep) itys tys]
  ]

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

-- taken from Leif-Erik Krueger
-- ---------------------------------------------------------------------------
-- Type Unification
-- ---------------------------------------------------------------------------

-- Tries to unify the two given lists of types and returns the unifying
-- substitution, if successful.
unifyTypeLists :: [Type] -> [Type] -> Maybe TypeSubst
unifyTypeLists []           []           = Just idSubst
unifyTypeLists (ty1 : tys1) (ty2 : tys2) = do
  sigma1 <- unifyTypeLists tys1 tys2
  sigma2 <- unifyTypes (subst sigma1 ty1) (subst sigma1 ty2)
  return $ sigma2 `compose` sigma1
unifyTypeLists _            _            = Nothing

unifyTypes :: Type -> Type -> Maybe TypeSubst
unifyTypes (TypeVariable tv1) (TypeVariable tv2)
  | tv1 == tv2            = Just idSubst
  | otherwise             = Just (singleSubst tv1 (TypeVariable tv2))
unifyTypes (TypeVariable tv) ty
  | tv `elem` typeVars ty = Nothing
  | otherwise             = Just (singleSubst tv ty)
unifyTypes ty (TypeVariable tv)
  | tv `elem` typeVars ty = Nothing
  | otherwise             = Just (singleSubst tv ty)
unifyTypes (TypeConstructor tc1) (TypeConstructor tc2)
  | tc1 == tc2 = Just idSubst
unifyTypes (TypeApply ty11 ty12) (TypeApply ty21 ty22) =
  unifyTypeLists [ty11, ty12] [ty21, ty22]
unifyTypes ty1@(TypeApply _ _) (TypeArrow ty21 ty22) =
  unifyTypes ty1 (TypeApply (TypeApply (TypeConstructor qArrowId) ty21) ty22)
unifyTypes (TypeArrow ty11 ty12) ty2@(TypeApply _ _) =
  unifyTypes (TypeApply (TypeApply (TypeConstructor qArrowId) ty11) ty12) ty2
unifyTypes (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
  unifyTypeLists [ty11, ty12] [ty21, ty22]
unifyTypes _ _ = Nothing
