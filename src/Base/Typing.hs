{- |
    Module      :  $Header$
    Description :  Type computation of Curry expressions
    Copyright   :  (c) 2003 - 2006 Wolfgang Lux
                       2014 - 2015 Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    After the compiler has attributed patterns and expressions with type
    information during type inference, it is straightforward to recompute
    the type of every pattern and expression. Since all annotated types
    are monomorphic, there is no need to instantiate any variables or
    perform any (non-trivial) unifications.
-}

module Base.Typing
  ( Typeable (..)
  , withType, matchPredType, matchPredType', matchPreds, matchPred, matchType
  , matchPredTypeSafe, matchPredTypeSafe', matchPredsSafe, matchPredSafe
  , matchTypesSafe, matchTypeSafe
  , bindDecls, bindDecl, bindPatterns, bindPattern, declVars, patternVars
  ) where

import           Data.List (nub)
import           Data.Maybe (fromMaybe, isJust)
import qualified Data.Map as Map

import Curry.Base.Ident
import Curry.Syntax

import GHC.Stack (HasCallStack)

import Debug.Trace

import Base.Messages (internalError)
import Base.PrettyTypes ()
import Base.Subst
import Base.Types
import Base.TypeSubst
import Base.Utils (fst3)

import Env.Value

class Typeable a where
  typeOf :: a -> Type

instance Typeable Type where
  typeOf = id

instance Typeable PredType where
  typeOf = unpredType

instance Typeable a => Typeable (Rhs a) where
  typeOf (SimpleRhs  _ _ e _ ) = typeOf e
  typeOf (GuardedRhs _ _ es _) = head [typeOf e | CondExpr _ _ e <- es]

instance Typeable a => Typeable (Pattern a) where
  typeOf (LiteralPattern _ a _) = typeOf a
  typeOf (NegativePattern _ a _) = typeOf a
  typeOf (VariablePattern _ a _) = typeOf a
  typeOf (ConstructorPattern _ a _ _) = typeOf a
  typeOf (InfixPattern _ a _ _ _) = typeOf a
  typeOf (ParenPattern _ t) = typeOf t
  typeOf (RecordPattern _ a _ _) = typeOf a
  typeOf (TuplePattern _ ts) = tupleType $ map typeOf ts
  typeOf (ListPattern _ a _) = typeOf a
  typeOf (AsPattern _ _ t) = typeOf t
  typeOf (LazyPattern _ t) = typeOf t
  typeOf (FunctionPattern _ a _ _) = typeOf a
  typeOf (InfixFuncPattern _ a _ _ _) = typeOf a

instance Typeable a => Typeable (Expression a) where
  typeOf (Literal _ a _) = typeOf a
  typeOf (Variable _ a _) = typeOf a
  typeOf (Constructor _ a _) = typeOf a
  typeOf (Paren _ e) = typeOf e
  typeOf (Typed _ e _) = typeOf e
  typeOf (Record _ a _ _) = typeOf a
  typeOf (RecordUpdate _ e _) = typeOf e
  typeOf (Tuple _ es) = tupleType (map typeOf es)
  typeOf (List _ a _) = typeOf a
  typeOf (ListCompr _ e _) = listType (typeOf e)
  typeOf (EnumFrom _ e) = listType (typeOf e)
  typeOf (EnumFromThen _ e _) = listType (typeOf e)
  typeOf (EnumFromTo _ e _) = listType (typeOf e)
  typeOf (EnumFromThenTo _ e _ _) = listType (typeOf e)
  typeOf (UnaryMinus _ e) = typeOf e
  typeOf (Apply _ e _) = case typeOf e of
    TypeArrow _ ty -> ty
    _ -> internalError "Base.Typing.typeOf: application"
  typeOf (InfixApply _ _ op _) = case typeOf (infixOp op) of
    TypeArrow _ (TypeArrow _ ty) -> ty
    _ -> internalError "Base.Typing.typeOf: infix application"
  typeOf (LeftSection _ _ op) = case typeOf (infixOp op) of
    TypeArrow _ ty -> ty
    _ -> internalError "Base.Typing.typeOf: left section"
  typeOf (RightSection _ op _) = case typeOf (infixOp op) of
    TypeArrow ty1 (TypeArrow _ ty2) -> TypeArrow ty1 ty2
    _ -> internalError "Base.Typing.typeOf: right section"
  typeOf (Lambda _ ts e) = foldr (TypeArrow . typeOf) (typeOf e) ts
  typeOf (Let _ _ _ e) = typeOf e
  typeOf (Do _ _ _ e) = typeOf e
  typeOf (IfThenElse _ _ e _) = typeOf e
  typeOf (Case _ _ _ _ as) = typeOf $ head as

instance Typeable a => Typeable (Alt a) where
  typeOf (Alt _ _ rhs) = typeOf rhs

-- When inlining variable and function definitions, the compiler must
-- eventually update the type annotations of the inlined expression. To
-- that end, the variable or function's annotated type and the type of
-- the inlined expression must be unified. Since the program is type
-- correct, this unification is just a simple one way matching where we
-- only need to match the type variables in the inlined expression's type
-- with the corresponding types in the variable or function's annotated
-- type.

unifyPredSafe :: IsPred a => a -> a -> Maybe TypeSubst
unifyPredSafe pr1 pr2 = unifyPredSafe' (getPred pr1) (getPred pr2)

unifyPredSafe' :: Pred -> Pred -> Maybe TypeSubst
unifyPredSafe' (Pred _ qcls1 tys1) (Pred _ qcls2 tys2)
  | qcls1 == qcls2 = unifyTypesSafe tys1 tys2
  | otherwise      = Nothing


unifyTypesSafe :: [Type] -> [Type] -> Maybe TypeSubst
unifyTypesSafe []         []         = Just idSubst
unifyTypesSafe (ty1:tys1) (ty2:tys2) = do
  theta  <- unifyTypesSafe tys1 tys2
  theta' <- unifyTypeSafe (subst theta ty1) (subst theta ty2)
  return (theta' `compose` theta)
unifyTypesSafe _           _         = Nothing

unifyTypeSafe :: Type -> Type -> Maybe TypeSubst
unifyTypeSafe (TypeVariable tv1) (TypeVariable tv2)
  | tv1 == tv2 = Just idSubst
  | otherwise  = Just $ singleSubst tv1 (TypeVariable tv2)
unifyTypeSafe (TypeVariable tv) ty
  | tv `elem` typeVars ty = Nothing
  | otherwise             = Just $ singleSubst tv ty
unifyTypeSafe ty (TypeVariable tv)
  | tv `elem` typeVars ty = Nothing
  | otherwise             = Just $ singleSubst tv ty
unifyTypeSafe (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2)
  | tv1  == tv2           = Just idSubst
  | tys1 == tys2          = Just $ singleSubst tv1 (TypeConstrained tys2 tv2)
unifyTypeSafe (TypeConstrained tys tv) ty =
  foldr (choose . unifyTypeSafe ty) Nothing tys
  where choose Nothing theta' = theta'
        choose (Just theta) _ = Just (bindSubst tv ty theta)
unifyTypeSafe ty (TypeConstrained tys tv) =
  foldr (choose . unifyTypeSafe ty) Nothing tys
  where choose Nothing theta' = theta'
        choose (Just theta) _ = Just (bindSubst tv ty theta)
unifyTypeSafe (TypeConstructor tc1) (TypeConstructor tc2)
  | tc1 == tc2            = Just idSubst
unifyTypeSafe (TypeApply ty11 ty12) (TypeApply ty21 ty22) =
  unifyTypesSafe [ty11,ty12] [ty21,ty22]
unifyTypeSafe (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
  unifyTypesSafe [ty11,ty12] [ty21,ty22]
unifyTypeSafe (TypeArrow ty11 ty12) ty2@(TypeApply _ _) =
  unifyTypeSafe (TypeApply (TypeApply (TypeConstructor qArrowId) ty11) ty12) ty2
unifyTypeSafe ty1@(TypeApply _ _) (TypeArrow ty21 ty22) =
  unifyTypeSafe ty1 (TypeApply (TypeApply (TypeConstructor qArrowId) ty21) ty22)
unifyTypeSafe _ _ = Nothing 

withType :: (Functor f, Typeable (f Type)) => Type -> f Type -> f Type
withType ty e = fmap (subst (matchType (typeOf e) ty idSubst)) e

matchPredTypeSafe :: PredType -> PredType -> TypeSubst -> Maybe TypeSubst
matchPredTypeSafe (PredType ps1 ty1) (PredType ps2 ty2) =
  matchPredTypeSafe' ps1 ty1 ps2 ty2

matchPredsSafe :: [Pred] -> [Pred] -> TypeSubst -> Maybe TypeSubst
matchPredsSafe []       []       theta = Just theta
matchPredsSafe (p1:ps1) (p2:ps2) theta = do
  theta'  <- matchPredSafe p1 p2 theta
  theta'' <- matchPredsSafe ps1 ps2 theta'
  return theta''
matchPredsSafe _         _       _     = Nothing

matchPredSafe :: Pred -> Pred -> TypeSubst -> Maybe TypeSubst
matchPredSafe (Pred _ qcls1 tys1) (Pred _ qcls2 tys2) theta
  | qcls1 == qcls2 = matchTypesSafe tys1 tys2 theta
  | otherwise      = Nothing

matchPredTypeSafe' :: [Pred] -> Type -> [Pred] -> Type -> TypeSubst 
                   -> Maybe TypeSubst
matchPredTypeSafe' ps1 ty1 ps2 ty2 theta = do
  theta'  <- matchPredsSafe ps1 ps2 theta
  theta'' <- matchTypeSafe ty1 ty2 theta'
  return theta''

matchTypesSafe :: [Type] -> [Type] -> TypeSubst -> Maybe TypeSubst
matchTypesSafe []         []         theta = Just theta
matchTypesSafe (ty1:tys1) (ty2:tys2) theta = do
  theta'  <- matchTypeSafe ty1 ty2 theta
  theta'' <- matchTypesSafe tys1 tys2 theta'
  return theta''
matchTypesSafe _          _          _     = Nothing

matchTypeSafe :: Type -> Type -> TypeSubst -> Maybe TypeSubst
matchTypeSafe (TypeVariable tv) ty theta
  | ty == TypeVariable tv                       = Just theta
  | isBound theta tv && substVar theta tv /= ty = Nothing
  | otherwise                                   = Just $ bindVar tv ty theta
 where isBound (Subst _ thetaMap) tv = isJust $ Map.lookup tv thetaMap
matchTypeSafe (TypeConstructor tc1) (TypeConstructor tc2) theta
  | tc1 == tc2 = Just theta
matchTypeSafe (TypeConstrained _ tv1) (TypeConstrained _ tv2) theta
  | tv1 == tv2 = Just theta
matchTypeSafe (TypeApply ty11 ty12) (TypeApply ty21 ty22) theta = do
  theta' <- matchTypeSafe ty11 ty21 theta
  theta'' <- matchTypeSafe ty12 ty22 theta'
  return theta''
matchTypeSafe (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) theta = do
  theta' <- matchTypeSafe ty11 ty21 theta
  theta'' <- matchTypeSafe ty12 ty22 theta'
  return theta''
matchTypeSafe (TypeApply ty11 ty12) (TypeArrow ty21 ty22) theta = do
  theta' <- matchTypeSafe ty11 (TypeApply (TypeConstructor qArrowId) ty21) theta
  theta'' <- matchTypeSafe ty12 ty22 theta'
  return theta''
matchTypeSafe (TypeArrow ty11 ty12) (TypeApply ty21 ty22) theta = do
  theta' <- matchTypeSafe (TypeApply (TypeConstructor qArrowId) ty11) ty21 theta
  theta'' <- matchTypeSafe ty12 ty22 theta'
  return theta''
matchTypeSafe (TypeForall _ ty1) (TypeForall _ ty2) theta 
  = matchTypeSafe ty1 ty2 theta
matchTypeSafe (TypeForall _ ty1) ty2                theta
  = matchTypeSafe ty1 ty2 theta
matchTypeSafe ty1                (TypeForall _ ty2) theta 
  = matchTypeSafe ty1 ty2 theta
matchTypeSafe _                  _                  _     = Nothing
 

matchPredType :: HasCallStack => PredType -> PredType -> TypeSubst -> TypeSubst
matchPredType (PredType ps1 ty1) (PredType ps2 ty2) =
  matchPredType' ps1 ty1 ps2 ty2

matchPredType' :: HasCallStack => [Pred] -> Type -> [Pred] -> Type -> TypeSubst -> TypeSubst
matchPredType' ps1 ty1 ps2 ty2 =
  matchType ty1 ty2 . matchPreds ps1 ps2

matchPreds :: HasCallStack => [Pred] -> [Pred] -> TypeSubst -> TypeSubst
matchPreds []       []       = id
matchPreds (p1:ps1) (p2:ps2) =
  matchPreds ps1 ps2 . matchPred p1 p2
matchPreds ps1      ps2      = 
  internalError $ "Base.Typing,matchPreds: " ++ show (map pPrint ps1) ++ " " ++ show (map pPrint ps2)

-- TODO : check if it is OK to ignore the ICC flag
matchPred :: HasCallStack => Pred -> Pred -> TypeSubst -> TypeSubst
matchPred pt1@(Pred _ qcls1 tys1) pt2@(Pred _ qcls2 tys2) 
  | qcls1 == qcls2 = matchTypes tys1 tys2
  | otherwise      
  = internalError $ "Base.Typing.matchPred: " ++ show (pPrintPrec 11 pt1) ++ " " ++ show (pPrintPrec 11 pt2) 

matchTypes :: HasCallStack => [Type] -> [Type] -> TypeSubst -> TypeSubst
matchTypes []         []         = id
matchTypes (ty1:tys1) (ty2:tys2) = --traceShow (pPrint (ty1:tys1), pPrint(ty2:tys2)) $
  matchTypes tys1 tys2 . matchType ty1 ty2
matchTypes tys1       tys2       = internalError $
  "Base.Typing.matchTypes: " ++ show tys1 ++ " " ++ show tys2 

matchType :: HasCallStack => Type -> Type -> TypeSubst -> TypeSubst
matchType ty1 ty2 = fromMaybe noMatch (matchType' ty1 ty2)
  where
    noMatch = internalError $ "Base.Typing.matchType: " ++
                                show (pPrintPrec 11 ty1) ++ " " ++ show (pPrintPrec 11 ty2)

matchType' :: HasCallStack => Type -> Type -> Maybe (TypeSubst -> TypeSubst)
matchType' (TypeVariable tv) ty
  | ty == TypeVariable tv = Just id
  | otherwise = Just (bindSubst tv ty)
matchType' (TypeConstructor tc1) (TypeConstructor tc2)
  | tc1 == tc2 = Just id
matchType' (TypeConstrained _ tv1) (TypeConstrained _ tv2)
  | tv1 == tv2 = Just id
matchType' (TypeApply ty11 ty12) (TypeApply ty21 ty22) =
  fmap (. matchType ty12 ty22) (matchType' ty11 ty21)
matchType' (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
  Just (matchType ty11 ty21 . matchType ty12 ty22)
matchType' (TypeApply ty11 ty12) (TypeArrow ty21 ty22) =
  fmap (. matchType ty12 ty22)
       (matchType' ty11 (TypeApply (TypeConstructor qArrowId) ty21))
matchType' (TypeArrow ty11 ty12) (TypeApply ty21 ty22) =
  fmap (. matchType ty12 ty22)
       (matchType' (TypeApply (TypeConstructor qArrowId) ty11) ty21)
matchType' (TypeForall _ ty1) (TypeForall _ ty2) = matchType' ty1 ty2
matchType' (TypeForall _ ty1) ty2 = matchType' ty1 ty2
matchType' ty1 (TypeForall _ ty2) = matchType' ty1 ty2
matchType' _ _ = Nothing

-- The functions 'bindDecls', 'bindDecl', 'bindPatterns' and 'bindPattern'
-- augment the value environment with the types of the entities defined in
-- local declaration groups and patterns, respectively, using the types from
-- their type annotations.

bindDecls :: (Eq t, Typeable t, ValueType t) => [Decl t] -> ValueEnv -> ValueEnv
bindDecls = flip $ foldr bindDecl

bindDecl :: (Eq t, Typeable t, ValueType t) => Decl t -> ValueEnv -> ValueEnv
bindDecl d vEnv = bindLocalVars (filter unbound $ declVars d) vEnv
  where unbound v = null $ lookupValue (fst3 v) vEnv

bindPatterns :: (Eq t, Typeable t, ValueType t) => [Pattern t] -> ValueEnv
             -> ValueEnv
bindPatterns = flip $ foldr bindPattern

bindPattern :: (Eq t, Typeable t, ValueType t) => Pattern t -> ValueEnv
            -> ValueEnv
bindPattern t vEnv = bindLocalVars (filter unbound $ patternVars t) vEnv
  where unbound v = null $ lookupValue (fst3 v) vEnv

-- TODO : correct this if necessary for the new label of function decls
declVars :: (Eq t, Typeable t, ValueType t) => Decl t -> [(Ident, Int, t)]
declVars (InfixDecl        _ _ _ _) = []
declVars (TypeSig            _ _ _) = []
declVars (FunctionDecl  _ ty f eqs) = [(f, eqnArity $ head eqs, ty)]
declVars (PatternDecl        _ t _) = patternVars t
declVars (FreeDecl            _ vs) = [(v, 0, ty) | Var ty v <- vs]
declVars _                          = internalError "Base.Typing.declVars"

patternVars :: (Eq t, Typeable t, ValueType t) => Pattern t -> [(Ident, Int, t)]
patternVars (LiteralPattern         _ _ _) = []
patternVars (NegativePattern        _ _ _) = []
patternVars (VariablePattern       _ ty v) = [(v, 0, ty)]
patternVars (ConstructorPattern  _ _ _ ts) = concatMap patternVars ts
patternVars (InfixPattern     _ _ t1 _ t2) = patternVars t1 ++ patternVars t2
patternVars (ParenPattern             _ t) = patternVars t
patternVars (RecordPattern       _ _ _ fs) =
  concat [patternVars t | Field _ _ t <- fs]
patternVars (TuplePattern            _ ts) = concatMap patternVars ts
patternVars (ListPattern           _ _ ts) = concatMap patternVars ts
patternVars (AsPattern              _ v t) =
  (v, 0, toValueType $ typeOf t) : patternVars t
patternVars (LazyPattern              _ t) = patternVars t
patternVars (FunctionPattern     _ _ _ ts) = nub $ concatMap patternVars ts
patternVars (InfixFuncPattern _ _ t1 _ t2) =
  nub $ patternVars t1 ++ patternVars t2
