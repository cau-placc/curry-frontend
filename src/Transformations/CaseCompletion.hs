{- |
    Module      :  $Header$
    Description :  CaseCompletion
    Copyright   :  (c) 2005       , Martin Engelke
                       2011 - 2015, Björn Peemöller
                       2016       , Jan Tikovsky
                       2016       , Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module expands case branches with missing constructors.

    The MCC translates case expressions into the intermediate language
    representation (IL) without completing them (i.e. without generating
    case branches for missing contructors), because the intermediate language
    supports variable patterns for the fallback case.
    In contrast, the FlatCurry representation of patterns only allows
    literal and constructor patterns, which requires the expansion
    default branches to all missing constructors.

    This is only necessary for *rigid* case expressions, because any
    *flexible* case expression with more than one branch and a variable
    pattern is non-deterministic. In consequence, these overlapping patterns
    have already been eliminated in the pattern matching compilation
    process (see module CurryToIL).

    To summarize, this module expands all rigid case expressions.
-}
{-# LANGUAGE CPP #-}
module Transformations.CaseCompletion (completeCase) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Monad              (replicateM)
import qualified Control.Monad.State as S   (State, evalState, gets, modify)
import           Data.List                  (find)
import           Data.Maybe                 (fromMaybe, listToMaybe)

import           Curry.Base.Ident
import qualified Curry.Syntax        as CS

import Base.Expr
import Base.Messages                        (internalError)
import Base.Types                           (charType, floatType, intType)

import Env.Interface                        (InterfaceEnv, lookupInterface)

import Transformations.Dictionary           (qImplMethodId)

import IL

-- Completes case expressions by adding branches for missing constructors.
-- The interface environment 'iEnv' is needed to compute these constructors.
completeCase :: InterfaceEnv -> Module -> Module
completeCase iEnv mdl@(Module mid is ds) = Module mid is ds'
 where ds'= S.evalState (mapM ccDecl ds) (CCState mdl iEnv 0)

-- -----------------------------------------------------------------------------
-- Internally used state monad
-- -----------------------------------------------------------------------------

data CCState = CCState
  { modul        :: Module
  , interfaceEnv :: InterfaceEnv
  , nextId       :: Int
  }

type CCM a = S.State CCState a

getModule :: CCM Module
getModule = S.gets modul

getInterfaceEnv :: CCM InterfaceEnv
getInterfaceEnv = S.gets interfaceEnv

-- Create a fresh identifier
freshIdent :: CCM Ident
freshIdent = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return $ mkIdent $ "_#comp" ++ show nid

-- -----------------------------------------------------------------------------
-- The following functions traverse an IL term searching for case expressions
-- -----------------------------------------------------------------------------

ccDecl :: Decl -> CCM Decl
ccDecl dd@(DataDecl        _ _ _) = return dd
ccDecl nt@(NewtypeDecl     _ _ _) = return nt
ccDecl (FunctionDecl qid vs ty e) = FunctionDecl qid vs ty <$> ccExpr e
ccDecl ed@(ExternalDecl  _ _ _ _) = return ed

ccExpr :: Expression -> CCM Expression
ccExpr l@(Literal       _) = return l
ccExpr v@(Variable      _) = return v
ccExpr f@(Function    _ _) = return f
ccExpr c@(Constructor _ _) = return c
ccExpr (Apply       e1 e2) = Apply <$> ccExpr e1 <*> ccExpr e2
ccExpr (Case      ea e bs) = do
  e'  <- ccExpr e
  bs' <- mapM ccAlt bs
  ccCase ea e' bs'
ccExpr (Or          e1 e2) = Or <$> ccExpr e1 <*> ccExpr e2
ccExpr (Exist         v e) = Exist v <$> ccExpr e
ccExpr (Let           b e) = Let <$> ccBinding b <*> ccExpr e
ccExpr (Letrec       bs e) = Letrec <$> mapM ccBinding bs <*> ccExpr e
ccExpr (Typed        e ty) = flip Typed ty <$> ccExpr e

ccAlt :: Alt -> CCM Alt
ccAlt (Alt p e) = Alt p <$> ccExpr e

ccBinding :: Binding -> CCM Binding
ccBinding (Binding v e) = Binding v <$> ccExpr e

-- ---------------------------------------------------------------------------
-- Functions for completing case alternatives
-- ---------------------------------------------------------------------------
ccCase :: Eval -> Expression -> [Alt] -> CCM Expression
-- flexible cases are not completed
ccCase Flex  e alts     = return $ Case Flex e alts
ccCase Rigid _ []       = internalError $ "CaseCompletion.ccCase: "
                                       ++ "empty alternative list"
ccCase Rigid e as@(Alt p _:_) = case p of
  ConstructorPattern _ _ -> completeConsAlts Rigid e as
  LiteralPattern     _   -> completeLitAlts  Rigid e as
  VariablePattern    _   -> completeVarAlts        e as

-- Completes a case alternative list which branches via constructor patterns
-- by adding alternatives. Thus, case expressions of the form
--     case <ce> of
--       <C_1> -> <expr_1>
--              :
--       <C_n> -> <expr_n>
--      [<var> -> <default_expr>]
-- are in general extended to
--     let x = <ce> in
--     let y = <default_expr>[<var>/x] in
--     case x of
--       <C_1>  -> <expr_1>
--               :
--       <C_n>  -> <expr_n>
--       <C'_1> -> y
--               :
--       <C'_m> -> y
-- where the C'_j are the complementary constructor patterns of the C_i,
-- @x@ and @y@ are fresh variables, and "default_expr" is the expression
-- from the first alternative containing a variable pattern. If there is no such
-- alternative, the default expression is set to the prelude function 'failed'.
-- In addition, there are a few optimizations performed to avoid the
-- construction of unnecessary let-bindings:
--   - If there are no complementary patterns, the expression remains unchanged.
--   - If there is only one complementary pattern,
--     the binding for @y@ is avoided (see @bindDefVar@).
--   - If the variable @<var>@ does not occur in the default expression,
--     the binding for @x@ is avoided (see @mkCase@).
completeConsAlts :: Eval -> Expression -> [Alt] -> CCM Expression
completeConsAlts ea ce alts = do
  mdl       <- getModule
  menv      <- getInterfaceEnv
  -- complementary constructor patterns
  complPats <- mapM genPat $ getComplConstrs mdl menv
               [ c | (Alt (ConstructorPattern c _) _) <- consAlts ]
  v <- freshIdent
  w <- freshIdent
  return $ case (complPats, defaultAlt v) of
            (_:_, Just e') -> bindDefVar v ce w e' complPats
            _              -> Case ea ce consAlts
  where
  -- existing contructor pattern alternatives
  consAlts = [ a | a@(Alt (ConstructorPattern _ _) _) <- alts ]

  -- generate a new constructor pattern
  genPat (qid, arity) = ConstructorPattern qid <$> replicateM arity freshIdent

  -- default alternative, if there is one
  defaultAlt v = listToMaybe [ replaceVar x (Variable v) e
                             | Alt (VariablePattern x) e <- alts ]

  -- create a binding for @v = e@ if needed
  bindDefVar v e w e' ps
    | v `elem` fv e' = mkBinding v e $ mkCase (Variable v) w e' ps
    | otherwise      = mkCase e w e' ps

  -- create a binding for @w = e'@ if needed, and a case expression
  -- @case e of { consAlts ++ (ps -> w) }@
  mkCase e w e' ps = case ps of
    [p] -> Case ea e (consAlts ++ [Alt p e'])
    _   -> mkBinding w e'
         $ Case ea e (consAlts ++ [Alt p (Variable w) | p <- ps])

-- If the alternatives' branches contain literal patterns, a complementary
-- constructor list cannot be generated because it would become potentially
-- infinite. Thus, function 'completeLitAlts' transforms case expressions like
--     case <ce> of
--       <lit_1> -> <expr_1>
--       <lit_2> -> <expr_2>
--                   :
--       <lit_n> -> <expr_n>
--      [<var>   -> <default_expr>]
-- to
--     let x = <ce> in
--     case (v == <lit_1>) of
--       True  -> <expr_1>
--       False -> case (x == <lit_2>) of
--                  True  -> <expr_2>
--                  False -> case ...
--                                 :
--                               -> case (x == <lit_n>) of
--                                    True  -> <expr_n>
--                                    False -> <default_expr>
-- If the default expression is missing, @failed@ is used instead.
completeLitAlts :: Eval -> Expression -> [Alt] -> CCM Expression
completeLitAlts ea ce alts = do
  x <- freshIdent
  return $ mkBinding x ce $ nestedCases x alts
  where
  nestedCases _ []              = failedExpr
  nestedCases x (Alt p ae : as) = case p of
    LiteralPattern l  -> Case ea (Variable x `eqExpr` Literal l)
                          [ Alt truePatt  ae
                          , Alt falsePatt (nestedCases x as)
                          ]
    VariablePattern v -> replaceVar v (Variable x) ae
    _ -> internalError "CaseCompletion.completeLitAlts: illegal alternative"

-- For the unusual case of only one alternative containing a variable pattern,
-- it is necessary to tranform it to a 'let' term because FlatCurry does not
-- support variable patterns in case alternatives. So the case expression
--    case <ce> of
--      x -> <ae>
-- is transformed to
--      let x = <ce> in <ae>
completeVarAlts :: Expression -> [Alt] -> CCM Expression
completeVarAlts _  []             = return failedExpr
completeVarAlts ce (Alt p ae : _) = case p of
  VariablePattern x -> return $ mkBinding x ce ae
  _                 -> internalError $
    "CaseCompletion.completeVarAlts: variable pattern expected"

-- Smart constructor for non-recursive let-binding. @mkBinding v e e'@
-- evaluates to @e'[v/e]@ if @e@ is a variable, or @let v = e in e'@ otherwise.
mkBinding :: Ident -> Expression -> Expression -> Expression
mkBinding v e e' = case e of
  Variable _ -> replaceVar v e e'
  _          -> Let (Binding v e) e'

-- ---------------------------------------------------------------------------
-- This part of the module contains functions for replacing variables
-- with expressions. This is necessary in the case of having a default
-- alternative like
--      v -> <expr>
-- where the variable v occurs in the default expression <expr>. When
-- building additional alternatives for this default expression, the variable
-- must be replaced with the newly generated constructors.
replaceVar :: Ident -> Expression -> Expression -> Expression
replaceVar v e x@(Variable    w)
  | v == w    = e
  | otherwise = x
replaceVar v e (Apply     e1 e2)
  = Apply (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Case   ev e' bs)
  = Case ev (replaceVar v e e') (map (replaceVarInAlt v e) bs)
replaceVar v e (Or        e1 e2)
  = Or (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Exist      w e')
   | v == w                     = Exist w e'
   | otherwise                  = Exist w (replaceVar v e e')
replaceVar v e (Let        b e')
   | v `occursInBinding` b      = Let b e'
   | otherwise                  = Let (replaceVarInBinding v e b)
                                      (replaceVar v e e')
replaceVar v e (Letrec    bs e')
   | any (occursInBinding v) bs = Letrec bs e'
   | otherwise                     = Letrec (map (replaceVarInBinding v e) bs)
                                            (replaceVar v e e')
replaceVar _ _ e'               = e'

replaceVarInAlt :: Ident -> Expression -> Alt -> Alt
replaceVarInAlt v e (Alt p e')
  | v `occursInPattern` p = Alt p e'
  | otherwise             = Alt p (replaceVar v e e')

replaceVarInBinding :: Ident -> Expression -> Binding -> Binding
replaceVarInBinding v e (Binding w e')
  | v == w    = Binding w e'
  | otherwise = Binding w (replaceVar v e e')

occursInPattern :: Ident -> ConstrTerm -> Bool
occursInPattern v (VariablePattern       w) = v == w
occursInPattern v (ConstructorPattern _ vs) = v `elem` vs
occursInPattern _ _                         = False

occursInBinding :: Ident -> Binding -> Bool
occursInBinding v (Binding w _) = v == w

-- ---------------------------------------------------------------------------
-- The following functions generate several IL expressions and patterns

failedExpr :: Expression
failedExpr = Function (qualifyWith preludeMIdent (mkIdent "failed")) 0

eqExpr :: Expression -> Expression -> Expression
eqExpr e1 e2 = Apply (Apply (Function eq 2) e1) e2
  where eq = qImplMethodId preludeMIdent qEqId ty $ mkIdent "=="
        ty = case e2 of
               Literal l -> case l of
                              Char  _ -> charType
                              Int   _ -> intType
                              Float _ -> floatType
               _ -> internalError "CaseCompletion.eqExpr: no literal"

truePatt :: ConstrTerm
truePatt = ConstructorPattern qTrueId []

falsePatt :: ConstrTerm
falsePatt = ConstructorPattern qFalseId []

-- ---------------------------------------------------------------------------
-- The following functions compute the missing constructors for generating
-- missing case alternatives

-- Computes the complementary constructors for a given list of constructors.
-- All specified constructors must be of the same type.
-- This functions uses the module environment 'menv', which contains all
-- imported constructors, except for the built-in list constructors.
-- TODO: Check if the list constructors are in the menv.
getComplConstrs :: Module -> InterfaceEnv -> [QualIdent] -> [(QualIdent, Int)]
getComplConstrs _                 _    []
  = internalError "CaseCompletion.getComplConstrs: empty constructor list"
getComplConstrs (Module mid _ ds) menv cs@(c:_)
  -- built-in lists
  | c `elem` [qNilId, qConsId] = complementary cs [(qNilId, 0), (qConsId, 2)]
  -- current module
  | mid' == mid                = getCCFromDecls cs ds
  -- imported module
  | otherwise                  = maybe [] (getCCFromIDecls mid' cs)
                                          (lookupInterface mid' menv)
  where mid' = fromMaybe mid (qidModule c)

-- Find complementary constructors within the declarations of the
-- current module
getCCFromDecls :: [QualIdent] -> [Decl] -> [(QualIdent, Int)]
getCCFromDecls cs ds = complementary cs cinfos
  where
  cinfos = map constrInfo
         $ maybe [] extractConstrDecls (find (`declares` head cs) ds)

  decl `declares` qid = case decl of
    DataDecl    _ _ cs' -> any (`declaresConstr` qid) cs'
    NewtypeDecl _ _ nc  -> nc `declaresConstr` qid
    _                   -> False

  declaresConstr (ConstrDecl cid _) qid = cid == qid

  extractConstrDecls (DataDecl _ _ cs') = cs'
  extractConstrDecls _                  = []

  constrInfo (ConstrDecl cid tys) = (cid, length tys)

-- Find complementary constructors within the module environment
getCCFromIDecls :: ModuleIdent -> [QualIdent] -> CS.Interface -> [(QualIdent, Int)]
getCCFromIDecls mid cs (CS.Interface _ _ ds) = complementary cs cinfos
  where
  cinfos = map constrInfo
         $ maybe [] extractConstrDecls (find (`declares` head cs) ds)

  decl `declares` qid = case decl of
    CS.IDataDecl    _ _ _ _ cs' _ -> any (`declaresConstr` qid) cs'
    CS.INewtypeDecl _ _ _ _ nc  _ -> isNewConstrDecl qid nc
    _                             -> False

  declaresConstr (CS.ConstrDecl  _ _ _ cid _) qid = unqualify qid == cid
  declaresConstr (CS.ConOpDecl _ _ _ _ oid _) qid = unqualify qid == oid
  declaresConstr (CS.RecordDecl  _ _ _ cid _) qid = unqualify qid == cid

  isNewConstrDecl qid (CS.NewConstrDecl _ cid _) = unqualify qid == cid
  isNewConstrDecl qid (CS.NewRecordDecl _ cid _) = unqualify qid == cid

  extractConstrDecls (CS.IDataDecl _ _ _ _ cs' _) = cs'
  extractConstrDecls _                            = []

  constrInfo (CS.ConstrDecl _ _ _ cid tys) = (qualifyWith mid cid, length tys)
  constrInfo (CS.ConOpDecl  _ _ _ _ oid _) = (qualifyWith mid oid, 2)
  constrInfo (CS.RecordDecl _ _ _ cid  fs) = (qualifyWith mid cid, length labels)
    where labels = [l | CS.FieldDecl _ ls _ <- fs, l <- ls]

-- Compute complementary constructors
complementary :: [QualIdent] -> [(QualIdent, Int)] -> [(QualIdent, Int)]
complementary known others = filter ((`notElem` known) . fst) others
