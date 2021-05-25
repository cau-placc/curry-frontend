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
  , toPredTypes, toConstrType, toMethodType
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
import Curry.Base.SpanInfo
import qualified Curry.Syntax as CS
import Curry.Syntax.Pretty (pPrint, pPrintPrec)

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
toType' _   (CS.ConstructorType _ tc) tys = applyType (TypeConstructor tc) tys
toType' tvs (CS.ApplyType  _ ty1 ty2) tys =
  toType' tvs ty1 (toType' tvs ty2 [] : tys)
toType' tvs (CS.VariableType    _ tv) tys =
  applyType (TypeVariable (toVar tvs tv)) tys
toType' tvs (CS.TupleType      _ tys) tys'
  | null tys  = internalError "Base.CurryTypes.toType': zero-element tuple"
  | null tys' = tupleType $ map ((flip $ toType' tvs) []) tys
  | otherwise = internalError "Base.CurryTypes.toType': tuple type application"
toType' tvs (CS.ListType        _ ty) tys
  | null tys  = listType $ toType' tvs ty []
  | otherwise = internalError "Base.CurryTypes.toType': list type application"
toType' tvs (CS.ArrowType  _ ty1 ty2) tys
  | null tys = TypeArrow (toType' tvs ty1 []) (toType' tvs ty2 [])
  | otherwise = internalError "Base.CurryTypes.toType': arrow type application"
toType' tvs (CS.ParenType       _ ty) tys = toType' tvs ty tys
toType' tvs (CS.ForallType _ tvs' ty) tys
  | null tvs' = toType' tvs ty tys
  | otherwise = applyType (TypeForall (map (toVar tvs) tvs')
                                      (toType' tvs ty []))
                          tys

toVar :: Map.Map Ident Int -> Ident -> Int
toVar tvs tv = case Map.lookup tv tvs of
  Just tv' -> tv'
  Nothing  -> internalError "Base.CurryTypes.toVar: unknown type variable"

toQualType :: ModuleIdent -> [Ident] -> CS.TypeExpr -> Type
toQualType m tvs = qualifyType m . toType tvs

toQualTypes :: ModuleIdent -> [Ident] -> [CS.TypeExpr] -> [Type]
toQualTypes m tvs = map (qualifyType m) . toTypes tvs

toPred :: [Ident] -> PredIsICC -> CS.Constraint -> Pred
toPred tvs isIcc c = toPred' (enumTypeVars tvs c) isIcc c

toPred' :: Map.Map Ident Int -> PredIsICC -> CS.Constraint -> Pred
toPred' tvs isIcc (CS.Constraint _ qcls tys) =
  Pred isIcc qcls (map (flip (toType' tvs) []) tys)

toQualPred :: ModuleIdent -> [Ident] -> PredIsICC -> CS.Constraint -> Pred
toQualPred m tvs fstIcc = qualifyPred m . toPred tvs fstIcc

toPredSet :: [Ident] -> PredIsICC -> CS.Context -> PredSet
toPredSet tvs fstIcc cx = toPredSet' (enumTypeVars tvs cx) fstIcc cx

toPredSet' :: Map.Map Ident Int -> PredIsICC -> CS.Context -> PredSet
toPredSet' tvs fstIcc =
  Set.fromList . zipWith (toPred' tvs) (fstIcc : repeat OPred)

toQualPredSet :: ModuleIdent -> [Ident] -> PredIsICC -> CS.Context -> PredSet
toQualPredSet m tvs fstIcc = qualifyPredSet m . toPredSet tvs fstIcc

toPredType :: [Ident] -> PredIsICC -> CS.QualTypeExpr -> PredType
toPredType tvs fstIcc qty = toPredType' (enumTypeVars tvs qty) fstIcc qty

toPredType' :: Map.Map Ident Int -> PredIsICC -> CS.QualTypeExpr -> PredType
toPredType' tvs fstIcc (CS.QualTypeExpr _ cx ty) =
  PredType (toPredSet' tvs fstIcc cx) (toType' tvs ty [])

toQualPredType ::
  ModuleIdent -> [Ident] -> PredIsICC -> CS.QualTypeExpr -> PredType
toQualPredType m tvs fstIcc = qualifyPredType m . toPredType tvs fstIcc

toPredTypes :: [Ident] -> PredIsICC -> CS.Context -> [CS.TypeExpr] -> PredTypes
toPredTypes tvs fstIcc cx tys =
  PredTypes (toPredSet' (enumTypeVars tvs tys) fstIcc cx) (toTypes tvs tys)

-- The function 'toConstrType' returns the type of a data or newtype
-- constructor. Hereby, it restricts the context to those type variables
-- which are free in the argument types.

toConstrType :: QualIdent -> [Ident] -> [CS.TypeExpr] -> PredType
toConstrType tc tvs tys = toPredType tvs OPred $
  CS.QualTypeExpr NoSpanInfo [] ty'
  where ty'  = foldr (CS.ArrowType NoSpanInfo) ty0 tys
        ty0  = foldl (CS.ApplyType NoSpanInfo)
                     (CS.ConstructorType NoSpanInfo tc)
                     (map (CS.VariableType NoSpanInfo) tvs)

-- The function 'toMethodType' returns the type of a type class method.
-- It adds the implicit type class constraint to the method's type signature and
-- ensures that the class' n type variables are always assigned indices 0 to
-- n-1.

toMethodType :: QualIdent -> [Ident] -> CS.QualTypeExpr -> PredType
toMethodType qcls clsvars (CS.QualTypeExpr spi cx ty) =
  toPredType clsvars ICC (CS.QualTypeExpr spi cx' ty)
  where cx' = CS.Constraint NoSpanInfo qcls
                (map (CS.VariableType NoSpanInfo) clsvars) : cx

fromType :: [Ident] -> Type -> CS.TypeExpr
fromType tvs ty = fromType' tvs ty []

fromType' :: [Ident] -> Type -> [CS.TypeExpr] -> CS.TypeExpr
fromType' _   (TypeConstructor    tc) tys
  | isQTupleId tc && qTupleArity tc == length tys
    = CS.TupleType NoSpanInfo tys
  | tc == qListId && length tys == 1
    = CS.ListType NoSpanInfo (head tys)
  | otherwise
  = foldl (CS.ApplyType NoSpanInfo) (CS.ConstructorType NoSpanInfo tc) tys
fromType' tvs (TypeApply     ty1 ty2) tys =
  fromType' tvs ty1 (fromType tvs ty2 : tys)
fromType' tvs (TypeVariable       tv) tys =
  foldl (CS.ApplyType NoSpanInfo) (CS.VariableType NoSpanInfo (fromVar tvs tv))
    tys
fromType' tvs (TypeArrow     ty1 ty2) tys =
  foldl (CS.ApplyType NoSpanInfo)
    (CS.ArrowType NoSpanInfo (fromType tvs ty1) (fromType tvs ty2)) tys
fromType' tvs (TypeConstrained tys _) tys' = fromType' tvs (head tys) tys'
fromType' tvs (TypeForall    tvs' ty) tys
  | null tvs' = fromType' tvs ty tys
  | otherwise = foldl (CS.ApplyType NoSpanInfo)
                      (CS.ForallType NoSpanInfo (map (fromVar tvs) tvs')
                                                (fromType tvs ty))
                      tys

fromVar :: [Ident] -> Int -> Ident
fromVar tvs tv = if tv >= 0 then tvs !! tv else mkIdent ('_' : show (-tv))

fromQualType :: ModuleIdent -> [Ident] -> Type -> CS.TypeExpr
fromQualType m tvs = fromType tvs . unqualifyType m

fromPred :: [Ident] -> Pred -> CS.Constraint
fromPred tvs (Pred _ qcls tys) =
  CS.Constraint NoSpanInfo qcls (map (fromType tvs) tys)

fromQualPred :: ModuleIdent -> [Ident] -> Pred -> CS.Constraint
fromQualPred m tvs = fromPred tvs . unqualifyPred m

-- Due to the sorting of the predicate set, the list of constraints is sorted
-- as well.

fromPredSet :: [Ident] -> PredSet -> CS.Context
fromPredSet tvs = map (fromPred tvs) . Set.toAscList

fromQualPredSet :: ModuleIdent -> [Ident] -> PredSet -> CS.Context
fromQualPredSet m tvs = fromPredSet tvs . unqualifyPredSet m

fromPredType :: [Ident] -> PredType -> CS.QualTypeExpr
fromPredType tvs (PredType ps ty) =
  CS.QualTypeExpr NoSpanInfo (fromPredSet tvs ps) (fromType tvs ty)

fromQualPredType :: ModuleIdent -> [Ident] -> PredType -> CS.QualTypeExpr
fromQualPredType m tvs = fromPredType tvs . unqualifyPredType m

-- The following functions implement pretty-printing for types.

ppType :: ModuleIdent -> Type -> Doc
ppType m = pPrintPrec 0 . fromQualType m identSupply

ppPred :: ModuleIdent -> Pred -> Doc
ppPred m = pPrint . fromQualPred m identSupply

ppPredType :: ModuleIdent -> PredType -> Doc
ppPredType m = pPrint . fromQualPredType m identSupply

ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
ppTypeScheme m (ForAll _ pty) = ppPredType m pty
