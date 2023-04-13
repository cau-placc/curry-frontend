{- |
    Module      :  $Header$
    Description :  Type expansion
    Copyright   :  (c) 2016 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements expansion of alias types in types and predicates.
-}

module Base.TypeExpansion
  ( module Base.TypeExpansion
  ) where

import Curry.Base.Ident
import Curry.Syntax

import Data.List (nub)

import Base.CurryTypes
import Base.Messages
import Base.Types
import Base.TypeSubst

import Env.Class
import Env.TypeConstructor

-- The function 'expandType' expands all type synonyms in a type
-- and also qualifies all type constructors with the name of the module
-- in which the type was defined. Similarly, 'expandPred' expands all
-- type synonyms in a predicate and also qualifies all class identifiers
-- with the name of the module in which the class was defined. The
-- function 'expandPredSet' minimizes the predicate set after expansion.

expandType :: ModuleIdent -> TCEnv -> Type -> Type
expandType m tcEnv ty = expandType' m tcEnv ty []

expandType' :: ModuleIdent -> TCEnv -> Type -> [Type] -> Type
expandType' m tcEnv (TypeConstructor     tc) tys =
  case qualLookupTypeInfo tc tcEnv of
    [DataType       tc' _ _ ] -> applyType (TypeConstructor tc') tys
    [RenamingType   tc' _ _ ] -> applyType (TypeConstructor tc') tys
    [AliasType    _ _   n ty] -> let (tys', tys'') = splitAt n tys
                                 in  applyType (expandAliasType tys' ty) tys''
    _ -> case qualLookupTypeInfo (qualQualify m tc) tcEnv of
      [DataType       tc' _ _ ] -> applyType (TypeConstructor tc') tys
      [RenamingType   tc' _ _ ] -> applyType (TypeConstructor tc') tys
      [AliasType    _ _   n ty] -> let (tys', tys'') = splitAt n tys
                                   in  applyType (expandAliasType tys' ty) tys''
      _ -> internalError $ "Base.TypeExpansion.expandType: " ++ show tc
expandType' m tcEnv (TypeApply      ty1 ty2) tys =
  expandType' m tcEnv ty1 (expandType m tcEnv ty2 : tys)
expandType' _ _     tv@(TypeVariable      _) tys = applyType tv tys
expandType' _ _     tc@(TypeConstrained _ _) tys = applyType tc tys
expandType' m tcEnv (TypeArrow      ty1 ty2) tys =
  applyType (TypeArrow (expandType m tcEnv ty1) (expandType m tcEnv ty2)) tys
expandType' m tcEnv (TypeForall      tvs ty) tys =
  applyType (TypeForall tvs (expandType m tcEnv ty)) tys

expandPred :: ModuleIdent -> TCEnv -> Pred -> Pred
expandPred m tcEnv (Pred isIcc qcls tys) = case qualLookupTypeInfo qcls tcEnv of
  [TypeClass ocls _ _] -> Pred isIcc ocls (map (expandType m tcEnv) tys)
  _ -> case qualLookupTypeInfo (qualQualify m qcls) tcEnv of
    [TypeClass ocls _ _] -> Pred isIcc ocls (map (expandType m tcEnv) tys)
    _ -> internalError $ "Base.TypeExpansion.expandPred: " ++ show qcls

expandPredList :: ModuleIdent -> TCEnv -> ClassEnv -> PredList -> PredList
expandPredList m tcEnv clsEnv = minPredList clsEnv . map (expandPred m tcEnv)

expandPredType :: ModuleIdent -> TCEnv -> ClassEnv -> PredType -> PredType
expandPredType m tcEnv clsEnv (PredType pls ty) =
  PredType (expandPredList m tcEnv clsEnv pls) (expandType m tcEnv ty)

expandPredTypes :: ModuleIdent -> TCEnv -> ClassEnv -> PredTypes -> PredTypes
expandPredTypes m tcEnv clsEnv (PredTypes pls tys) =
  PredTypes (expandPredList m tcEnv clsEnv pls) (map (expandType m tcEnv) tys)

-- The functions 'expandMonoType', 'expandPolyType' and 'expandInst' convert
-- type expressions, qualified type expressions and instance contexts with lists
-- of instance types into (predicated) types and also expand all type synonyms
-- and qualify all type constructors during the conversion.

expandMonoType :: ModuleIdent -> TCEnv -> [Ident] -> TypeExpr -> Type
expandMonoType m tcEnv tvs = expandType m tcEnv . toType tvs

expandPolyType
  :: PredIsICC -> ModuleIdent -> TCEnv -> ClassEnv -> QualTypeExpr -> PredType
expandPolyType fstIcc m tcEnv clsEnv =
  normalize 0 . expandPredType m tcEnv clsEnv . toPredType [] fstIcc

expandInst
  :: ModuleIdent -> TCEnv -> ClassEnv -> Context -> [InstanceType] -> PredTypes
expandInst m tcEnv clsEnv cx =
  normalize 0 . expandPredTypes m tcEnv clsEnv . toPredTypes [] OPred cx

--taken from Leif-Erik Krueger
expandClassContext :: ModuleIdent -> TCEnv -> [Ident] -> Context -> PredList
expandClassContext m tcEnv clsvars =
  nub . map (expandPred m tcEnv) . toPredList clsvars OPred

-- The function 'expandConstrType' computes the predicated type for a data
-- or newtype constructor. Similar to 'toConstrType' from 'CurryTypes', the
-- type's context is restricted to those type variables which are free in
-- the argument types. However, type synonyms are expanded and type constructors
-- and type classes are qualified with the name of the module containing their
-- definition.

expandConstrType :: ModuleIdent -> TCEnv -> ClassEnv -> QualIdent -> [Ident]
                 -> [TypeExpr] -> PredType
expandConstrType m tcEnv clsEnv tc tvs tys =
  normalize n $ expandPredType m tcEnv clsEnv pty
  where n = length tvs
        pty = toConstrType tc tvs tys

-- The function 'expandMethodType' converts the type of a type class method.
-- Similar to the function 'toMethodType' from 'CurryTypes', the implicit class
-- constraint is added to the method's type and the class' n type variables are
-- assigned indices 0 to n-1. However, type synonyms are expanded and type
-- constructors and type classes are qualified with the name of the module
-- containing their definition.

expandMethodType :: ModuleIdent -> TCEnv -> ClassEnv -> QualIdent -> [Ident]
                 -> QualTypeExpr -> PredType
expandMethodType m tcEnv clsEnv qcls tvs =
  normalize (length tvs) . expandPredType m tcEnv clsEnv . toMethodType qcls tvs
