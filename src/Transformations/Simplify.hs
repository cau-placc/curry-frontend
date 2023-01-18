{- |
    Module      :  $Header$
    Description :  Optimizing the Desugared Code
    Copyright   :  (c) 2003        Wolfgang Lux
                                   Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After desugaring the source code, but before lifting local
   declarations, the compiler performs a few simple optimizations to
   improve the efficiency of the generated code. In addition, the
   optimizer replaces pattern bindings with simple variable bindings and
   selector functions.

   Currently, the following optimizations are implemented:

     * Under certain conditions, inline local function definitions.
     * Remove unused declarations.
     * Compute minimal binding groups for let expressions.
     * Remove pattern bindings to constructor terms
     * Inline simple constants.
-}
{-# LANGUAGE CPP #-}
module Transformations.Simplify (simplify) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Monad.Extra        (concatMapM)
import           Control.Monad.State as S   (State, runState, gets, modify)
import qualified Data.Map            as Map (Map, empty, insert, lookup)

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax

import Base.Expr
import Base.Messages (internalError)
import Base.SCC
import Base.Types
import Base.Typing
import Base.Utils

import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

-- -----------------------------------------------------------------------------
-- Simplification
-- -----------------------------------------------------------------------------

simplify :: ValueEnv -> Module Type -> (Module Type, ValueEnv)
simplify vEnv mdl@(Module _ _ _ m _ _ _) = (mdl', valueEnv s')
  where (mdl', s') = S.runState (simModule mdl) (SimplifyState m vEnv 1)

-- -----------------------------------------------------------------------------
-- Internal state monad
-- -----------------------------------------------------------------------------

data SimplifyState = SimplifyState
  { moduleIdent :: ModuleIdent -- read-only!
  , valueEnv    :: ValueEnv    -- updated for new pattern selection functions
  , nextId      :: Int         -- counter
  }

type SIM = S.State SimplifyState

getModuleIdent :: SIM ModuleIdent
getModuleIdent = S.gets moduleIdent

getNextId :: SIM Int
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

getFunArity :: QualIdent -> SIM Int
getFunArity f = do
  vEnv <- getValueEnv
  return $ case qualLookupValue f vEnv of
    [Value _ _ a _] -> a
    [Label   _ _ _] -> 1
    _               -> internalError $ "Simplify.funType " ++ show f

getValueEnv :: SIM ValueEnv
getValueEnv = S.gets valueEnv

freshIdent :: (Int -> Ident) -> SIM Ident
freshIdent f = f <$> getNextId

-- -----------------------------------------------------------------------------
-- Simplification
-- -----------------------------------------------------------------------------

simModule :: Module Type -> SIM (Module Type)
simModule (Module spi li ps m es is ds) = Module spi li ps m es is
                                       <$> mapM (simDecl Map.empty) ds

-- Inline an expression for a variable
type InlineEnv = Map.Map Ident (Expression Type)

simDecl :: InlineEnv -> Decl Type -> SIM (Decl Type)
simDecl env (FunctionDecl p ty f eqs) = FunctionDecl p ty f
                                        <$> concatMapM (simEquation env) eqs
simDecl env (PatternDecl     p t rhs) = PatternDecl p t <$> simRhs env rhs
simDecl _   d                         = return d

simEquation :: InlineEnv -> Equation Type -> SIM [Equation Type]
simEquation env (Equation p a lhs rhs) = do
  rhs'  <- simRhs env rhs
  inlineFun env p a lhs rhs'

simRhs :: InlineEnv -> Rhs Type -> SIM (Rhs Type)
simRhs env (SimpleRhs  p _ e _) = simpleRhs p <$> simExpr env e
simRhs _   (GuardedRhs _ _ _ _) = error "Simplify.simRhs: guarded rhs"

-- -----------------------------------------------------------------------------
-- Inlining of Functions
-- -----------------------------------------------------------------------------

-- After simplifying the right hand side of an equation, the compiler
-- transforms declarations of the form
--
--   f t_1 ... t_{k-l} x_{k-l+1} ... x_k =
--     let g y_1 ... y_l = e
--     in  g x_{k-l+1} ... x_k
--
-- into the equivalent definition
--
--   f t_1 ... t_{k-l} x_{k-l+1} x_k = let y_1   = x_{k-l+1}
--                                              ...
--                                         y_l   = x_k
--                                     in  e
--
-- where the arities of 'f' and 'g' are 'k' and 'l', respectively, and
-- 'x_{k-l+1}, ... ,x_k' are variables. The transformation can obviously be
-- generalized to the case where 'g' is defined by more than one equation.
-- However, we must be careful not to change the evaluation mode of arguments.
-- Therefore, the transformation is applied only all of the arguments of 'g'
-- are variables.
--
-- This transformation is actually just a special case of inlining a
-- (local) function definition. We are unable to handle the general case
-- because it would require to represent the pattern matching code
-- explicitly in a Curry expression.

inlineFun :: InlineEnv -> SpanInfo -> Maybe Type -> Lhs Type -> Rhs Type
          -> SIM [Equation Type]
inlineFun env p ma lhs rhs = do
  m <- getModuleIdent
  case rhs of
    SimpleRhs _ _ (Let _ _ [FunctionDecl _ _ f' eqs'] e) _
      | -- @f'@ is not recursive
        f' `notElem` qfv m eqs'
        -- @f'@ does not perform any pattern matching
        && and [all isVariablePattern ts1 | Equation _ _ (FunLhs _ _ ts1) _ <- eqs']
      -> do
        let a = eqnArity $ head eqs'
            (n, vs', e') = etaReduce 0 [] (reverse (snd $ flatLhs lhs)) e
        if  -- the eta-reduced rhs of @f@ is a call to @f'@
            setSpanInfo NoSpanInfo e' == Variable NoSpanInfo (typeOf e') (qualify f')
            -- @f'@ was fully applied before eta-reduction
            && n  == a
          then mapM (mergeEqns p vs') eqs'
          else return [Equation p ma lhs rhs]
    _ -> return [Equation p ma lhs rhs]
  where
  etaReduce n1 vs (VariablePattern _ ty v : ts1)
                  (Apply _ e1 (Variable _ _ v'))
    | qualify v == v' = etaReduce (n1 + 1) ((ty, v) : vs) ts1 e1
  etaReduce n1 vs _ e1 = (n1, vs, e1)

  mergeEqns p1 vs (Equation _ _ (FunLhs _ _ ts2) (SimpleRhs p2 _ e _))
    = Equation p1 Nothing lhs <$> simRhs env (simpleRhs p2 (mkLet ds e))
      where
      ds = zipWith (\t v -> PatternDecl NoSpanInfo t (simpleRhs p2 (uncurry mkVar v)))
                   ts2
                   vs
  mergeEqns _ _ _ = error "Simplify.inlineFun.mergeEqns: no pattern match"

-- -----------------------------------------------------------------------------
-- Simplification of Expressions
-- -----------------------------------------------------------------------------

-- Variables that are bound to (simple) constants and aliases to other
-- variables are substituted. In terms of conventional compiler technology,
-- these optimizations correspond to constant propagation and copy propagation,
-- respectively. The transformation is applied recursively to a substituted
-- variable in order to handle chains of variable definitions.

-- Applications of let-expressions and case-expressions to other expressions
-- are simplified according to the following rules:
--   (let ds in e_1)            e_2 -> let ds in (e1 e2)
--   (case e_1 of p'_n -> e'_n) e_2 -> case e_1 of p'_n -> (e'n e_2)

-- The bindings of a let expression are sorted topologically in
-- order to split them into minimal binding groups. In addition,
-- local declarations occurring on the right hand side of a pattern
-- declaration are lifted into the enclosing binding group using the
-- equivalence (modulo alpha-conversion) of 'let x = let ds in e_1 in e_2'
-- and 'let ds; x = e_1 in e_2'.
-- This transformation avoids the creation of some redundant lifted
-- functions in later phases of the compiler.

simExpr :: InlineEnv -> Expression Type -> SIM (Expression Type)
simExpr _   l@(Literal     _ _ _) = return l
simExpr _   c@(Constructor _ _ _) = return c
-- subsitution of variables
simExpr env v@(Variable   _ ty x)
  | isQualified x = return v
  | otherwise     =
    maybe (return v) (simExpr env . withType ty) (Map.lookup (unqualify x) env)
-- simplification of application
simExpr env (Apply       _ e1 e2) = case e1 of
  Let _ _ ds e'     -> simExpr env (mkLet ds (Apply NoSpanInfo e' e2))
  Case _ _ ct e' bs -> simExpr env (mkCase ct e' (map (applyToAlt e2) bs))
  _                 -> Apply NoSpanInfo <$> simExpr env e1 <*> simExpr env e2
  where
  applyToAlt e (Alt        p t rhs) = Alt p t (applyToRhs e rhs)
  applyToRhs e (SimpleRhs  p _ e1' _) = simpleRhs p (Apply NoSpanInfo e1' e)
  applyToRhs _ (GuardedRhs _ _ _ _) = error "Simplify.simExpr.applyRhs: Guarded rhs"
-- simplification of declarations
simExpr env (Let        _ _ ds e) = do
  m   <- getModuleIdent
  dss <- mapM sharePatternRhs ds
  simplifyLet env (scc bv (qfv m) (foldr hoistDecls [] (concat dss))) e
simExpr env (Case    _ _ ct e bs) =
  mkCase ct <$> simExpr env e <*> mapM (simplifyAlt env) bs
simExpr env (Typed       _ e qty) =
  flip (Typed NoSpanInfo) qty <$> simExpr env e
simExpr _   _                     = error "Simplify.simExpr: no pattern match"

-- Simplify a case alternative
simplifyAlt :: InlineEnv -> Alt Type -> SIM (Alt Type)
simplifyAlt env (Alt p t rhs) = Alt p t <$> simRhs env rhs

-- Transform a pattern declaration @t = e@ into two declarations
-- @t = v, v = e@ whenever @t@ is not a variable. This is used to share
-- the expression @e@ using the fresh variable @v@.
sharePatternRhs :: Decl Type -> SIM [Decl Type]
--TODO: change to patterns instead of case
sharePatternRhs (PatternDecl p t rhs) = case t of
  VariablePattern _ _ _ -> return [PatternDecl p t rhs]
  _                     -> do
    let ty = typeOf t
    v  <- freshIdent patternId
    return [ PatternDecl p t                      (simpleRhs p (mkVar ty v))
           , PatternDecl p (VariablePattern NoSpanInfo ty v) rhs
           ]
  where patternId n = mkIdent ("_#pat" ++ show n)
sharePatternRhs d                     = return [d]

-- Lift up nested let declarations in pattern declarations, i.e., replace
-- @let p = let ds' in e'; ds in e@ by @let ds'; p = e'; ds in e@.
hoistDecls :: Decl a -> [Decl a] -> [Decl a]
hoistDecls (PatternDecl p t (SimpleRhs p' _ (Let _ _ ds' e) _)) ds
 = foldr hoistDecls ds (PatternDecl p t (simpleRhs p' e) : ds')
hoistDecls d ds = d : ds

-- The declaration groups of a let expression are first processed from
-- outside to inside, simplifying the right hand sides and collecting
-- inlineable expressions on the fly. At present, only simple constants
-- and aliases to other variables are inlined. A constant is considered
-- simple if it is either a literal, a constructor, or a non-nullary
-- function. Note that it is not possible to define nullary functions in
-- local declarations in Curry. Thus, an unqualified name always refers
-- to either a variable or a non-nullary function. Applications of
-- constructors and partial applications of functions to at least one
-- argument are not inlined because the compiler has to allocate space
-- for them, anyway. In order to prevent non-termination, recursive
-- binding groups are not processed for inlining.

-- With the list of inlineable expressions, the body of the let is
-- simplified and then the declaration groups are processed from inside
-- to outside to construct the simplified, nested let expression. In
-- doing so, unused bindings are discarded. In addition, all pattern
-- bindings are replaced by simple variable declarations using selector
-- functions to access the pattern variables.

simplifyLet :: InlineEnv -> [[Decl Type]] -> Expression Type
            -> SIM (Expression Type)
simplifyLet env []       e = simExpr env e
simplifyLet env (ds:dss) e = do
  m     <- getModuleIdent
  ds'   <- mapM (simDecl env) ds  -- simplify declarations
  env'  <- inlineVars env ds'     -- inline a simple variable binding
  e'    <- simplifyLet env' dss e -- simplify remaining bindings
  ds''  <- concatMapM (expandPatternBindings (qfv m ds' ++ qfv m e')) ds'
  return $ foldr (mkLet' m) e' (scc bv (qfv m) ds'')

inlineVars :: InlineEnv -> [Decl Type] -> SIM InlineEnv
inlineVars env ds = case ds of
  [PatternDecl _ (VariablePattern _ _ v) (SimpleRhs _ _ e _)] -> do
    allowed <- canInlineVar v e
    return $ if allowed then Map.insert v e env else env
  _ -> return env
  where
  canInlineVar _ (Literal     _ _ _) = return True
  canInlineVar _ (Constructor _ _ _) = return True
  canInlineVar v (Variable   _ _ v')
    | isQualified v'             = (> 0) <$> getFunArity v'
    | otherwise                  = return $ v /= unqualify v'
  canInlineVar _ _               = return False

mkLet' :: ModuleIdent -> [Decl Type] -> Expression Type -> Expression Type
mkLet' m [FreeDecl p vs] e
  | null vs'  = e
  | otherwise = mkLet [FreeDecl p vs'] e -- remove unused free variables
  where vs' = filter ((`elem` qfv m e) . varIdent) vs
mkLet' m [PatternDecl _ (VariablePattern _ ty v) (SimpleRhs _ _ e _)] (Variable _ _ v')
  | v' == qualify v && v `notElem` qfv m e = withType ty e -- inline single binding
mkLet' m ds e
  | not (any (`elem` qfv m e) (bv ds)) = e -- removed unused bindings
  | otherwise                              = mkLet ds e

-- In order to implement lazy pattern matching in local declarations,
-- pattern declarations 't = e' where 't' is not a variable
-- are transformed into a list of declarations
-- 'v_0 = e; v_1 = f_1 v_0; ...; v_n = f_n v_0' where 'v_0' is a fresh
-- variable, 'v_1,...,v_n' are the variables occurring in 't' and the
-- auxiliary functions 'f_i' are defined by 'f_i t = v_i' (see also
-- appendix D.8 of the Curry report). The bindings 'v_0 = e' are introduced
-- before splitting the declaration groups of the enclosing let expression
-- (cf. the 'Let' case in 'simExpr' above) so that they are placed in their own
-- declaration group whenever possible. In particular, this ensures that
-- the new binding is discarded when the expression 'e' is itself a variable.

-- fvs contains all variables used in the declarations and the body
-- of the let expression.
expandPatternBindings :: [Ident] -> Decl Type -> SIM [Decl Type]
expandPatternBindings fvs d@(PatternDecl p t (SimpleRhs _ _ e _)) = case t of
  VariablePattern _ _ _ -> return [d]
  _                     ->
    -- used variables
    mapM mkSelectorDecl (filter ((`elem` fvs) . fst3) (patternVars t))
  where
    pty = typeOf t -- type of pattern
    mkSelectorDecl (v, _, vty) = do
      let fty = TypeArrow pty vty
      f <- freshIdent (updIdentName (++ '#' : idName v) . fpSelectorId)
      return $ varDecl p vty v $
        mkLet [funDecl p fty f [t] (mkVar vty v)]
        (Apply NoSpanInfo (mkVar fty f) e)
expandPatternBindings _ d = return [d]
