{- |
    Module      :  $Header$
    Description :  Conversion of type representation
    Copyright   :  (c)         Wolfgang Lux
                   2011 - 2012 Björn Peemöller
                   2015        Jan Tikovsky
                   2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The functions 'toType', 'toTypes', and 'fromType' convert Curry type
   expressions into types and vice versa. The functions 'qualifyType' and
   'unqualifyType' add and remove module qualifiers in a type, respectively.

   When Curry type expression are converted with 'toType' or 'toTypes',
   type variables are assigned ascending indices in the order of their
   occurrence. It is possible to pass a list of additional type variables
   to both functions which are assigned indices before those variables
   occurring in the type. This allows preserving the order of type variables
   in the left hand side of a type declaration.
-}

module Base.CurryTypes
  ( toType, toTypes, toQualType, toQualTypes
  , toPred, toQualPred, toPredSet, toQualPredSet, toPredType, toQualPredType
  , toConstrType, toMethodType
  , fromType, fromQualType
  , fromPred, fromQualPred, fromPredSet, fromQualPredSet, fromPredType
  , fromQualPredType
  , ppType, ppPred, ppPredType, ppTypeScheme
  ) where

import Data.List (nub)
import qualified Data.Map as Map (Map, fromList, lookup)
import qualified Data.Set as Set

import Curry.Base.Ident
import Curry.Base.Pretty (Doc)
import qualified Curry.Syntax as CS
import Curry.Syntax.Pretty (ppConstraint, ppTypeExpr, ppQualTypeExpr)

import Base.Expr
import Base.Messages (internalError)
import Base.Types

enumTypeVars :: (Expr a, QuantExpr a) => [Ident] -> a -> Map.Map Ident Int
enumTypeVars tvs ty = Map.fromList $ zip (tvs ++ tvs') [0..]
  where
    tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs] ++
             [tv | tv <- nub (bv ty), tv `notElem` tvs]

toType :: [Ident] -> CS.TypeExpr -> Type
toType tvs ty = toType' (enumTypeVars tvs ty) ty []

toTypes :: [Ident] -> [CS.TypeExpr] -> [Type]
toTypes tvs tys = map ((flip (toType' (enumTypeVars tvs tys))) []) tys

toType' :: Map.Map Ident Int -> CS.TypeExpr -> [Type] -> Type
toType' _   (CS.ConstructorType tc) tys = applyType (TypeConstructor tc) tys
toType' tvs (CS.ApplyType  ty1 ty2) tys =
  toType' tvs ty1 (toType' tvs ty2 [] : tys)
toType' tvs (CS.VariableType    tv) tys =
  applyType (TypeVariable (toVar tvs tv)) tys
toType' tvs (CS.TupleType      tys) tys'
  | null tys  = internalError "Base.CurryTypes.toType': zero-element tuple"
  | null tys' = tupleType $ map ((flip $ toType' tvs) []) tys
  | otherwise = internalError "Base.CurryTypes.toType': tuple type application"
toType' tvs (CS.ListType        ty) tys
  | null tys  = listType $ toType' tvs ty []
  | otherwise = internalError "Base.CurryTypes.toType': list type application"
toType' tvs (CS.ArrowType  ty1 ty2) tys
  | null tys = TypeArrow (toType' tvs ty1 []) (toType' tvs ty2 [])
  | otherwise = internalError "Base.CurryTypes.toType': arrow type application"
toType' tvs (CS.ParenType       ty) tys = toType' tvs ty tys
toType' tvs (CS.ForallType tvs' ty) tys
  | null tvs' = toType' tvs ty tys
  | otherwise = applyType (TypeForall (map (toVar tvs) tvs') (toType' tvs ty []))
                          tys

toVar :: Map.Map Ident Int -> Ident -> Int
toVar tvs tv = case Map.lookup tv tvs of
  Just tv' -> tv'
  Nothing  -> internalError "Base.CurryTypes.toVar: unknown type variable"

toQualType :: ModuleIdent -> [Ident] -> CS.TypeExpr -> Type
toQualType m tvs = qualifyType m . toType tvs

toQualTypes :: ModuleIdent -> [Ident] -> [CS.TypeExpr] -> [Type]
toQualTypes m tvs = map (qualifyType m) . toTypes tvs

toPred :: [Ident] -> CS.Constraint -> Pred
toPred tvs c = toPred' (enumTypeVars tvs c) c

toPred' :: Map.Map Ident Int -> CS.Constraint -> Pred
toPred' tvs (CS.Constraint qcls ty) = Pred qcls (toType' tvs ty [])

toQualPred :: ModuleIdent -> [Ident] -> CS.Constraint -> Pred
toQualPred m tvs = qualifyPred m . toPred tvs

toPredSet :: [Ident] -> CS.Context -> PredSet
toPredSet tvs cx = toPredSet' (enumTypeVars tvs cx) cx

toPredSet' :: Map.Map Ident Int -> CS.Context -> PredSet
toPredSet' tvs = Set.fromList . map (toPred' tvs)

toQualPredSet :: ModuleIdent -> [Ident] -> CS.Context -> PredSet
toQualPredSet m tvs = qualifyPredSet m . toPredSet tvs

toPredType :: [Ident] -> CS.QualTypeExpr -> PredType
toPredType tvs qty = toPredType' (enumTypeVars tvs qty) qty

toPredType' :: Map.Map Ident Int -> CS.QualTypeExpr -> PredType
toPredType' tvs (CS.QualTypeExpr cx ty) =
  PredType (toPredSet' tvs cx) (toType' tvs ty [])

toQualPredType :: ModuleIdent -> [Ident] -> CS.QualTypeExpr -> PredType
toQualPredType m tvs = qualifyPredType m . toPredType tvs

-- The function 'toConstrType' returns the type of a data or newtype
-- constructor. Hereby, it restricts the context to those type variables
-- which are free in the argument types.

toConstrType :: QualIdent -> [Ident] -> CS.Context -> [CS.TypeExpr] -> PredType
toConstrType tc tvs cx tys = toPredType tvs $ CS.QualTypeExpr cx' ty'
  where tvs' = nub (fv tys)
        cx'  = restrictContext tvs' cx
        ty'  = foldr CS.ArrowType ty0 tys
        ty0  = foldl CS.ApplyType
                     (CS.ConstructorType tc)
                     (map CS.VariableType tvs)

restrictContext :: [Ident] -> CS.Context -> CS.Context
restrictContext tvs cx =
  [CS.Constraint cls ty | CS.Constraint cls ty <- cx, classVar ty `elem` tvs]
  where classVar (CS.VariableType tv) = tv
        classVar (CS.ApplyType  ty _) = classVar ty
        classVar _ = internalError "Base.CurryTypes.restrictContext.classVar"

-- The function 'toMethodType' returns the type of a type class method.
-- It adds the implicit type class constraint to the method's type signature
-- and ensures that the class' type variable is always assigned index 0.

toMethodType :: QualIdent -> Ident -> CS.QualTypeExpr -> PredType
toMethodType qcls clsvar (CS.QualTypeExpr cx ty) =
  toPredType [clsvar] (CS.QualTypeExpr cx' ty)
  where cx' = CS.Constraint qcls (CS.VariableType clsvar) : cx

fromType :: [Ident] -> Type -> CS.TypeExpr
fromType tvs ty = fromType' tvs ty []

fromType' :: [Ident] -> Type -> [CS.TypeExpr] -> CS.TypeExpr
fromType' _   (TypeConstructor    tc) tys
  | isQTupleId tc && qTupleArity tc == length tys = CS.TupleType tys
  | tc == qListId && length tys == 1              = CS.ListType (head tys)
  | otherwise
  = foldl CS.ApplyType (CS.ConstructorType tc) tys
fromType' tvs (TypeApply     ty1 ty2) tys =
  fromType' tvs ty1 (fromType tvs ty2 : tys)
fromType' tvs (TypeVariable       tv) tys =
  foldl CS.ApplyType (CS.VariableType (fromVar tvs tv)) tys
fromType' tvs (TypeArrow     ty1 ty2) tys =
  foldl CS.ApplyType (CS.ArrowType (fromType tvs ty1) (fromType tvs ty2)) tys
fromType' tvs (TypeConstrained tys _) tys' = fromType' tvs (head tys) tys'
fromType' _   (TypeSkolem          k) tys =
  foldl CS.ApplyType (CS.VariableType $ mkIdent $ "_?" ++ show k) tys
fromType' tvs (TypeForall    tvs' ty) tys
  | null tvs' = fromType' tvs ty tys
  | otherwise = foldl CS.ApplyType
                      (CS.ForallType (map (fromVar tvs) tvs') (fromType tvs ty))
                      tys

fromVar :: [Ident] -> Int -> Ident
fromVar tvs tv = if tv >= 0 then tvs !! tv else mkIdent ('_' : show (-tv))

fromQualType :: ModuleIdent -> [Ident] -> Type -> CS.TypeExpr
fromQualType m tvs = fromType tvs . unqualifyType m

fromPred :: [Ident] -> Pred -> CS.Constraint
fromPred tvs (Pred qcls ty) = CS.Constraint qcls (fromType tvs ty)

fromQualPred :: ModuleIdent -> [Ident] -> Pred -> CS.Constraint
fromQualPred m tvs = fromPred tvs .  unqualifyPred m

-- Due to the sorting of the predicate set, the list of constraints is sorted
-- as well.

fromPredSet :: [Ident] -> PredSet -> CS.Context
fromPredSet tvs = map (fromPred tvs) . Set.toAscList

fromQualPredSet :: ModuleIdent -> [Ident] -> PredSet -> CS.Context
fromQualPredSet m tvs = fromPredSet tvs . unqualifyPredSet m

fromPredType :: [Ident] -> PredType -> CS.QualTypeExpr
fromPredType tvs (PredType ps ty) =
  CS.QualTypeExpr (fromPredSet tvs ps) (fromType tvs ty)

fromQualPredType :: ModuleIdent -> [Ident] -> PredType -> CS.QualTypeExpr
fromQualPredType m tvs = fromPredType tvs . unqualifyPredType m

-- The following functions implement pretty-printing for types.

ppType :: ModuleIdent -> Type -> Doc
ppType m = ppTypeExpr 0 . fromQualType m identSupply

ppPred :: ModuleIdent -> Pred -> Doc
ppPred m = ppConstraint . fromQualPred m identSupply

ppPredType :: ModuleIdent -> PredType -> Doc
ppPredType m = ppQualTypeExpr . fromQualPredType m identSupply

ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
ppTypeScheme m (ForAll _ pty) = ppPredType m pty
