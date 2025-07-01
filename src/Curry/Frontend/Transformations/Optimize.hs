{- |
    Module      : Curry.Frontend.Transformations.Optimize
    Description : Optimization transformations for Curry expressions
    Copyright   : (c) 2025 Kai-Oliver Prott
    License     : BSD-3-clause

    Maintainer  : kpr@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This module implements optimization transformations for Curry in the intermediate language (IL).
    We assume that the input is already case completed.
    At the moment it does:
    - Remove unused variables in 'Let' expressions
    - Inline single-use variables in 'Let' expressions
    - Desugar case expressions where the scrutinee is of a known constructor
-}
{-# LANGUAGE LambdaCase #-}
module Curry.Frontend.Transformations.Optimize (optimize) where

import Data.List            (find)
import Data.Foldable        (foldrM)
import Control.Monad.Reader (Reader, runReader, local, ask)

import Curry.Base.Ident ( Ident )
import Curry.Frontend.Base.Subst
    ( Subst, idSubst, bindSubst, unbindSubst, substVar' )
import Curry.Frontend.CompilerOpts
    ( OptimizationOpts(optInlineLet, optCaseOfKnown) )
import Curry.Frontend.IL.Type
    ( Binding(Binding), Alt(..), Eval, Expression(..)
    , ConstrTerm(..), Decl(..), Module(..), Type )

data OptEnv = OptEnv
  { subst        :: Subst Ident Expression,
    opts         :: OptimizationOpts
  }

-- | The main entry point for the optimization transformation.
-- It takes an 'OptimizationOpts' and an intermediate language 'Module',
-- and returns an optimized 'Module
optimize :: OptimizationOpts -> Module -> Module
optimize o (Module mid imp ds) = Module mid imp (map optimizeDecl ds)
  where
    optimizeDecl :: Decl -> Decl
    optimizeDecl (FunctionDecl qualId args retType body) =
      FunctionDecl qualId args retType $
      runReader (optimizeExpr body) (OptEnv idSubst o)
    optimizeDecl d = d

optimizeExpr :: Expression ->  Reader OptEnv Expression
optimizeExpr (Variable ty i) = substVar ty i
optimizeExpr (Apply e1 e2) = Apply <$> optimizeExpr e1 <*> optimizeExpr e2
optimizeExpr (Case ct e alts) = optimizeCase ct e alts
optimizeExpr (Or e1 e2) = Or <$> optimizeExpr e1 <*> optimizeExpr e2
optimizeExpr (Exist i t e) = Exist i t <$> without [i] (optimizeExpr e)
optimizeExpr (Let (Binding i e1) e2) = optimizeLet i e1 e2
optimizeExpr (Letrec bds e) = without (map (\(Binding i _) -> i) bds) $ do
  bds' <- mapM (\(Binding i e') -> Binding i <$> optimizeExpr e') bds
  e' <- optimizeExpr e
  return $ Letrec bds' e'
optimizeExpr (Typed e t) = Typed <$> optimizeExpr e <*> return t
optimizeExpr e = return e

-- | Optimize a case expression.
-- If the scrutinee is a known constructor, it desugars the case expression
-- by inlining the constructor's arguments into the body of the matching alternative.
-- Otherwise, it leaves the case expression unchanged.
-- This optimization is controlled by the 'optCaseOfKnown' option.
optimizeCase :: Eval -> Expression -> [Alt] -> Reader OptEnv Expression
optimizeCase ct e1 alts = do
  env <- ask
  e1' <- optimizeExpr e1
  if not (optCaseOfKnown (opts env))
    then Case ct e1' <$> mapM optimizeAlt alts
    else do
      let (f, args) = unapplyExpr e1'
      case f of
        Constructor _ qid _ |
          Just (Alt (ConstructorPattern _ _ vs) e2)
              <- find (matchAlt qid) alts
           -> optimizeExpr (mkLet (zip (map snd vs) args) e2)
        _ -> Case ct e1' <$> mapM optimizeAlt alts
  where
    mkLet :: [(Ident, Expression)] -> Expression -> Expression
    mkLet bindings body = foldr (\(i, e) acc -> Let (Binding i e) acc) body bindings

    matchAlt qid (Alt (ConstructorPattern _ qid' _) _) = qid == qid'
    matchAlt _ _ = False

    unapplyExpr = unapplyExpr' []
    unapplyExpr' args (Apply e1' e2') = unapplyExpr' (e2' : args) e1'
    unapplyExpr' args e' = (e', args)

    optimizeAlt (Alt conT e') = do
      e'' <- without (constrVars conT) $ optimizeExpr e'
      return $ Alt conT e''

-- | Optimize a 'Let' expression.
-- If the bound variable is used only once in the body, it inlines the variable.
-- If it is used more than once, it keeps the 'Let' expression.
-- If the variable is never used, it removes the 'Let' expression.
-- This optimization is controlled by the 'optInlineLet' option.
optimizeLet :: Ident -> Expression -> Expression -> Reader OptEnv Expression
optimizeLet i e1 e2 = without [i] $ do
  env <- ask
  if not (optInlineLet (opts env))
    then do
      e1' <- optimizeExpr e1
      e2' <- optimizeExpr e2
      return $ Let (Binding i e1') e2'
    else do
      occ <- getOccurrence i e2
      case occ of
        Never -> optimizeExpr e2
        Once -> do
          e1' <- optimizeExpr e1
          extend i e1' $ optimizeExpr e2
        More -> do
          e1' <- optimizeExpr e1
          e2' <- optimizeExpr e2
          return $ Let (Binding i e1') e2'

-------------------------------------------------------------------
-- Occurrence analysis
-------------------------------------------------------------------

data Occ = Never | Once | More
  deriving (Eq, Show)

-- | Get the occurrence of a variable in an expression.
-- It returns 'Never' if the variable is not used,
-- 'Once' if it is used exactly once,
-- and 'More' if it is used more than once.
-- This function is used to determine whether to inline a variable in a 'Let' expression.
-- It needs the substitution environment to resolve variable references correctly.
getOccurrence :: Ident -> Expression -> Reader OptEnv Occ
getOccurrence i (Variable ty i') = substVar ty i' >>= \case
  Variable  _ i'' | i'' == i -> return Once
  Variable _ _               -> return Never
  e                          -> getOccurrence i e
getOccurrence i (Apply e1 e2) = addM (getOccurrence i e1) (getOccurrence i e2)
getOccurrence i (Case _ e alts) = addM (getOccurrence i e) $
  foldrM (\(Alt conT e') acc -> addM (return acc) (without
      (constrVars conT)
      (getOccurrence i e')))
     Never alts
getOccurrence i (Or e1 e2) = addM (getOccurrence i e1) (getOccurrence i e2)
getOccurrence i (Exist i' _ _) | i == i' = return Never
getOccurrence i (Exist i' _ e) = without [i'] $ getOccurrence i e
getOccurrence i (Let (Binding i' _) _) | i == i' = return Never
getOccurrence i (Let (Binding i' e1) e2) = do
  addM (getOccurrence i e1) $
    without [i'] $ getOccurrence i e2
getOccurrence i (Letrec bds e) = do
  let is = map (\(Binding i' _) -> i') bds
  case find (== i) is of
    Just _ -> return Never
    Nothing -> without is $ do
      foldrM (\e' acc -> addM (return acc) (getOccurrence i e'))
        Never
        (e : map (\(Binding _ e') -> e') bds)
getOccurrence i (Typed e _) = getOccurrence i e
getOccurrence _ _ = return Never

-- | Add two occurrences together.
-- It is lazy in the second argument,
-- meaning that it will not evaluate the second occurrence if the first one is 'More'.
-- This is useful for combining occurrences from different parts of an expression.
addM :: Reader OptEnv Occ -> Reader OptEnv Occ -> Reader OptEnv Occ
addM r1 r2 = do
  o1 <- r1
  case o1 of
    More -> return More
    Never -> r2
    Once -> do
      o2 <- r2
      case o2 of
        Never -> return Once
        _     -> return More

-------------------------------------------------------------------
-- Substitutions
-------------------------------------------------------------------

without :: [Ident] -> Reader OptEnv a -> Reader OptEnv a
without is = local (\(OptEnv s o) -> OptEnv (foldr unbindSubst s is) o)

extend :: Ident -> Expression -> Reader OptEnv a -> Reader OptEnv a
extend i e = local (\(OptEnv s o) -> OptEnv (bindSubst i e s) o)

substVar :: Type -> Ident -> Reader OptEnv Expression
substVar ty i = do
  env <- ask
  return $ substVar' (Variable ty) subst' (subst env) i

subst' :: Subst Ident Expression -> Expression -> Expression
subst' s (Variable ty i) = substVar' (Variable ty) subst' s i
subst' s (Apply e1 e2) = Apply (subst' s e1) (subst' s e2)
subst' s (Case ct e alts) = Case ct (subst' s e) (map (substAlt s) alts)
  where
    substAlt :: Subst Ident Expression -> Alt -> Alt
    substAlt s' (Alt conT e') = Alt conT (subst' s' e')
subst' s (Or e1 e2) = Or (subst' s e1) (subst' s e2)
subst' s (Exist i ty e) = Exist i ty (subst' s e)
subst' s (Let (Binding i e1) e2) =
  Let (Binding i (subst' s e1)) (subst' s e2)
subst' s (Letrec bds e) =
  Letrec (map (\(Binding i e1) -> Binding i (subst' s e1)) bds) (subst' s e)
subst' s (Typed e ty) = Typed (subst' s e) ty
subst' _ e = e

-------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------

constrVars :: ConstrTerm -> [Ident]
constrVars (ConstructorPattern _ _ vs) = map snd vs
constrVars (VariablePattern _ v) = [v]
constrVars _ = []
