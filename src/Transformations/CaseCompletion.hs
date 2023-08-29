{- |
    Module      :  $Header$
    Description :  CaseCompletion
    Copyright   :  (c) 2005        Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2016        Jan Tikovsky
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

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




import qualified Control.Monad.State as S   (State, evalState, gets, modify)
import           Data.List                  (find)
import           Data.Maybe                 (fromMaybe, listToMaybe)

import           Curry.Base.Ident
import qualified Curry.Syntax        as CS

import Base.Expr
import Base.Messages                        (internalError)
import Base.Types                           ( charType, floatType
                                            , intType, stringType
                                            )
import qualified Base.Types as CS
import Base.Subst

import Env.TypeConstructor
import Env.Interface                        (InterfaceEnv, lookupInterface)

import Transformations.CurryToIL            (transType)
import Transformations.Dictionary           (qImplMethodId, qDictTypeId, qInstFunId)

import IL

-- Completes case expressions by adding branches for missing constructors.
-- The interface environment 'iEnv' is needed to compute these constructors.
completeCase :: InterfaceEnv -> TCEnv -> Module -> Module
completeCase iEnv tcEnv mdl@(Module mid is ds) = Module mid is ds'
 where ds'= S.evalState (mapM ccDecl ds) (CCState mdl iEnv 0 tcEnv )

-- -----------------------------------------------------------------------------
-- Internally used state monad
-- -----------------------------------------------------------------------------

data CCState = CCState
  { modul        :: Module
  , interfaceEnv :: InterfaceEnv
  , nextId       :: Int
  , tyconEnv     :: TCEnv
  }

type CCM a = S.State CCState a

getModule :: CCM Module
getModule = S.gets modul

getTCEnv :: CCM TCEnv
getTCEnv = S.gets tyconEnv

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
ccDecl edd@(ExternalDataDecl _ _) = return edd
ccDecl (FunctionDecl qid vs ty e) = FunctionDecl qid vs ty <$> ccExpr e
ccDecl ed@(ExternalDecl    _ _ _) = return ed
ccDecl nd@(NewtypeDecl     _ _ _) = return nd

ccExpr :: Expression -> CCM Expression
ccExpr l@(Literal       _ _) = return l
ccExpr v@(Variable      _ _) = return v
ccExpr f@(Function    _ _ _) = return f
ccExpr c@(Constructor _ _ _) = return c
ccExpr (Apply         e1 e2) = Apply <$> ccExpr e1 <*> ccExpr e2
ccExpr (Case        ea e bs) = do
  e'  <- ccExpr e
  bs' <- mapM ccAlt bs
  ccCase ea e' bs'
ccExpr (Or            e1 e2) = Or <$> ccExpr e1 <*> ccExpr e2
ccExpr (Exist        v ty e) = Exist v ty <$> ccExpr e
ccExpr (Let             b e) = Let <$> ccBinding b <*> ccExpr e
ccExpr (Letrec         bs e) = Letrec <$> mapM ccBinding bs <*> ccExpr e
ccExpr (Typed          e ty) = flip Typed ty <$> ccExpr e

ccAlt :: Alt -> CCM Alt
ccAlt (Alt p e) = Alt p <$> ccExpr e

ccBinding :: Binding -> CCM Binding
ccBinding (Binding v e) = Binding v <$> ccExpr e

-- ---------------------------------------------------------------------------
-- Functions for completing case alternatives
-- ---------------------------------------------------------------------------
ccCase :: Eval -> Expression -> [Alt] -> CCM Expression
-- flexible cases are not completed, but literal string pats are transformed.
ccCase Flex  e alts     = return $ Case Flex e alts
ccCase Rigid _ []       = internalError $ "CaseCompletion.ccCase: "
                                       ++ "empty alternative list"
ccCase Rigid e as@(Alt p _:_) = case p of
  VariablePattern    _ _   -> completeVarAlts        e as
  _ | any isLitPat as -> completeLitAlts Rigid e as
    | otherwise       -> completeConsAlts Rigid e as
  where
    isLitPat (Alt (LiteralPattern _ _) _) = True
    isLitPat _                            = False

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
  tcEnv     <- getTCEnv
  -- complementary constructor patterns
  complPats <- mapM genPat $ getComplConstrs mdl menv tcEnv
               [ c | (Alt (ConstructorPattern _ c _) _) <- consAlts ]
  v <- freshIdent
  w <- freshIdent
  return $ case (complPats, defaultAlt v) of
            (_:_, Just e') -> bindDefVar v ce w e' complPats
            _              -> Case ea ce consAlts
  where
  -- existing contructor pattern alternatives
  consAlts = [ a | a@(Alt (ConstructorPattern _ _ _) _) <- alts ]

  -- unifier for data type and concrete pattern type
  dataTy  = case patTy of
              TypeConstructor qid tys
                -> TypeConstructor qid $ map TypeVariable [0 .. length tys - 1]
              _ -> internalError "CaseCompletion.completeConsAlt: not a type constructor"
  patTy   = let Alt pat _ = head consAlts in typeOf pat
  tySubst = matchType dataTy patTy idSubst

  -- generate a new constructor pattern
  genPat (qid, tys) = ConstructorPattern patTy qid <$>
    mapM (\ty' -> freshIdent >>= \v -> return (ty', v)) (subst tySubst tys)

  -- default alternative, if there is one
  defaultAlt v = listToMaybe [ replaceVar x (Variable ty v) e
                             | Alt (VariablePattern ty x) e <- alts ]

  -- create a binding for @v = e@ if needed
  bindDefVar v e w e' ps
    | v `elem` fv e' = mkBinding v e $ mkCase (Variable (typeOf e) v) w e' ps
    | otherwise      = mkCase e w e' ps

  -- create a binding for @w = e'@ if needed, and a case expression
  -- @case e of { consAlts ++ (ps -> w) }@
  mkCase e w e' ps = case ps of
    [p] -> Case ea e (consAlts ++ [Alt p e'])
    _   -> mkBinding w e'
         $ Case ea e (consAlts ++ [Alt p (Variable (typeOf e') w) | p <- ps])

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
  mkBinding x ce <$> nestedCases x alts
  where
  nestedCases _ []              = return $ failedExpr (typeOf $ head alts)
  nestedCases x (Alt p ae : as) = case p of
    LiteralPattern ty l  -> do
      as' <- nestedCases x as
      return $ Case ea (eqExpr (litType l) ty (Variable ty x) (completeLit l ty))
                  [ Alt truePatt  ae
                  , Alt falsePatt as'
                  ]
    VariablePattern ty v -> return $ replaceVar v (Variable ty x) ae
    ConstructorPattern ty@(TypeConstructor _ [ty']) c vs
      | c == qNilId  -> do
        i <- freshIdent
        j <- freshIdent
        as' <- nestedCases x as
        return $ Case ea ce [ Alt (ConstructorPattern ty c vs) ae
                            , Alt (ConstructorPattern ty qConsId [(ty', i), (ty, j)]) as']
      | c == qConsId -> do
        as' <- nestedCases x as
        return $ Case ea ce [ Alt (ConstructorPattern ty c vs) ae
                            , Alt (ConstructorPattern ty qNilId []) as']
    _ -> internalError "CaseCompletion.completeLitAlts: illegal alternative"

litType :: Literal -> CS.Type
litType (String _) = stringType
litType (Char _) = charType
litType (Int _) = intType
litType (Float _) = floatType

-- translate literal string in case to a list of characters
completeLit :: Literal -> Type -> Expression
completeLit (String s) ty = foldr mkCons mkNil s
    where
      consTy = TypeArrow charType' (TypeArrow ty ty)
      mkNil = IL.Constructor ty qNilId 0
      mkCons c = IL.Apply (IL.Apply (Constructor consTy qConsId 2) (IL.Literal charType' (Char c)))
completeLit x ty = Literal ty x

-- For the unusual case of only one alternative containing a variable pattern,
-- it is necessary to tranform it to a 'let' term because FlatCurry does not
-- support variable patterns in case alternatives. So the case expression
--    case <ce> of
--      x -> <ae>
-- is transformed to
--      let x = <ce> in <ae>
completeVarAlts :: Expression -> [Alt] -> CCM Expression
completeVarAlts _  []             = internalError
  "CaseCompletion.completeVarAlts: empty alternative list"
completeVarAlts ce (Alt p ae : _) = case p of
  VariablePattern _ x -> return $ mkBinding x ce ae
  _                   -> internalError
    "CaseCompletion.completeVarAlts: variable pattern expected"

-- Smart constructor for non-recursive let-binding. @mkBinding v e e'@
-- evaluates to @e'[v/e]@ if @e@ is a variable, or @let v = e in e'@ otherwise.
mkBinding :: Ident -> Expression -> Expression -> Expression
mkBinding v e e' = case e of
  Variable _ _ -> replaceVar v e e'
  _            -> Let (Binding v e) e'

-- ---------------------------------------------------------------------------
-- This part of the module contains functions for replacing variables
-- with expressions. This is necessary in the case of having a default
-- alternative like
--      v -> <expr>
-- where the variable v occurs in the default expression <expr>. When
-- building additional alternatives for this default expression, the variable
-- must be replaced with the newly generated constructors.
replaceVar :: Ident -> Expression -> Expression -> Expression
replaceVar v e x@(Variable  _ w)
  | v == w    = e
  | otherwise = x
replaceVar v e (Apply     e1 e2)
  = Apply (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Case   ev e' bs)
  = Case ev (replaceVar v e e') (map (replaceVarInAlt v e) bs)
replaceVar v e (Or        e1 e2)
  = Or (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Exist   w ty e')
   | v == w                     = Exist w ty e'
   | otherwise                  = Exist w ty (replaceVar v e e')
replaceVar v e (Let        b e')
   | v `occursInBinding` b      = Let b e'
   | otherwise                  = Let (replaceVarInBinding v e b)
                                      (replaceVar v e e')
replaceVar v e (Letrec    bs e')
   | any (occursInBinding v) bs = Letrec bs e'
   | otherwise                  = Letrec (map (replaceVarInBinding v e) bs)
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
occursInPattern v (VariablePattern       _ w) = v == w
occursInPattern v (ConstructorPattern _ _ vs) = v `elem` map snd vs
occursInPattern _ _                           = False

occursInBinding :: Ident -> Binding -> Bool
occursInBinding v (Binding w _) = v == w

-- ---------------------------------------------------------------------------
-- The following functions generate several IL expressions and patterns

failedExpr :: Type -> Expression
failedExpr ty = Function ty (qualifyWith preludeMIdent (mkIdent "failed")) 0

--TODO: Add note about arity of 0 because of the predefined functions in the Prelude
eqExpr :: CS.Type -> IL.Type -> Expression -> Expression -> Expression
eqExpr ty ty' e1 | IL.TypeConstructor _ [_] <- ty'
  = Apply (Apply (Apply (Function eqListTy eqList 0)
                    (Function dataCharDictType dataCharDict 0)) e1)
  where eqList = qImplMethodId preludeMIdent qDataId ty $ mkIdent "==="
        eqListTy = TypeArrow (IL.TypeConstructor (qDictTypeId qDataId) [ty'])
                     (TypeArrow ty' (TypeArrow ty' boolType'))
        dataCharDict = qInstFunId preludeMIdent qDataId charType
        dataCharDictType = TypeArrow unitType' (IL.TypeConstructor (qDictTypeId qDataId) [charType'])
eqExpr ty ty' e1 =
    Apply (Apply (Function eqTy eq 0) e1)
  where eq   = qImplMethodId preludeMIdent qDataId ty $ mkIdent "==="
        eqTy = TypeArrow ty' (TypeArrow ty' boolType')

truePatt :: ConstrTerm
truePatt = ConstructorPattern boolType' qTrueId []

falsePatt :: ConstrTerm
falsePatt = ConstructorPattern boolType' qFalseId []

boolType' :: Type
boolType' = IL.TypeConstructor qBoolId []

charType' :: Type
charType' = IL.TypeConstructor qCharId []

unitType' :: Type
unitType' = IL.TypeConstructor qUnitId []

-- ---------------------------------------------------------------------------
-- The following functions compute the missing constructors for generating
-- missing case alternatives

-- Computes the complementary constructors for a given list of constructors.
-- All specified constructors must be of the same type.
-- This functions uses the module environment 'menv', which contains all
-- imported constructors, except for the built-in list constructors.
-- TODO: Check if the list constructors are in the menv.
getComplConstrs :: Module -> InterfaceEnv -> TCEnv
                -> [QualIdent] -> [(QualIdent, [Type])]
getComplConstrs _                 _    _     []
  = internalError "CaseCompletion.getComplConstrs: empty constructor list"
getComplConstrs (Module mid _ ds) menv tcEnv cs@(c:_)
  -- built-in lists
  | c `elem` [qNilId, qConsId] = complementary cs
    [ (qNilId, [])
    , (qConsId, [TypeVariable 0, TypeConstructor qListId [TypeVariable 0]])
    ]
  -- current module
  | mid' == mid                = getCCFromDecls cs ds
  -- imported module
  | otherwise                  = maybe [] (getCCFromIDecls mid' cs tcEnv)
                                          (lookupInterface mid' menv)
  where mid' = fromMaybe mid (qidModule c)

-- Find complementary constructors within the declarations of the
-- current module
getCCFromDecls :: [QualIdent] -> [Decl] -> [(QualIdent, [Type])]
getCCFromDecls cs ds = complementary cs cinfos
  where
  cinfos = map constrInfo
         $ maybe [] extractConstrDecls (find (`declares` head cs) ds)

  decl `declares` qid = case decl of
    DataDecl    _ _ cs' -> any (`declaresConstr` qid) cs'
    _                   -> False

  declaresConstr (ConstrDecl cid _) qid = cid == qid

  extractConstrDecls (DataDecl _ _ cs') = cs'
  extractConstrDecls _                  = []

  constrInfo (ConstrDecl cid tys) = (cid, tys)

-- Find complementary constructors within the module environment
getCCFromIDecls :: ModuleIdent -> [QualIdent] -> TCEnv -> CS.Interface
                -> [(QualIdent, [Type])]
getCCFromIDecls mid cs tcEnv (CS.Interface _ _ ds) = complementary cs cinfos
  where
  cinfos = map (uncurry constrInfo)
         $ maybe [] extractConstrDecls (find (`declares` head cs) ds)

  decl `declares` qid = case decl of
    CS.IDataDecl    _ _ _ _ cs' _ -> any (`declaresConstr` qid) cs'
    CS.INewtypeDecl _ _ _ _ nc  _ -> isNewConstrDecl qid nc
    _                             -> False

  declaresConstr (CS.ConstrDecl   _ cid _) qid = unqualify qid == cid
  declaresConstr (CS.ConOpDecl _ _ oid _) qid = unqualify qid == oid
  declaresConstr (CS.RecordDecl  _ cid _) qid = unqualify qid == cid

  isNewConstrDecl qid (CS.NewConstrDecl _ cid _) = unqualify qid == cid
  isNewConstrDecl qid (CS.NewRecordDecl _ cid _) = unqualify qid == cid

  extractConstrDecls (CS.IDataDecl _ _ _ vs cs' _) = zip (repeat vs) cs'
  extractConstrDecls _                             = []

  constrInfo vs (CS.ConstrDecl _ cid tys)     =
    (qualifyWith mid cid, map (transType' vs) tys)
  constrInfo vs (CS.ConOpDecl  _ ty1 oid ty2) =
    (qualifyWith mid oid, map (transType' vs) [ty1, ty2])
  constrInfo vs (CS.RecordDecl _ cid  fs)     =
    ( qualifyWith mid cid
    , [transType' vs ty | CS.FieldDecl _ ls ty <- fs, _ <- ls]
    )

  transType' vs = qualType . transType tcEnv . CS.toType vs

  qualType (TypeConstructor qid vs) = TypeConstructor (qualQualify mid qid) (map qualType vs)
  qualType (TypeArrow ty1 ty2)   = TypeArrow (qualType ty1) (qualType ty2)
  qualType (TypeVariable tv)     = TypeVariable tv
  qualType (TypeForall tvs ty)   = TypeForall tvs (qualType ty)

-- Compute complementary constructors
complementary :: [QualIdent] -> [(QualIdent, [Type])] -> [(QualIdent, [Type])]
complementary known = filter ((`notElem` known) . fst)

-- ---------------------------------------------------------------------------
-- The following section contains defintions to compute a type substitution
-- for generating the type annotations for missing case alternatives

type TypeSubst = Subst Int Type

class SubstType a where
  subst :: TypeSubst -> a -> a

instance SubstType a => SubstType [a] where
  subst sigma = map (subst sigma)

instance SubstType Type where
  subst sigma (TypeConstructor q tys) = TypeConstructor q $ subst sigma tys
  subst sigma (TypeVariable tv)       = substVar' TypeVariable subst sigma tv
  subst sigma (TypeArrow ty1 ty2)
    = TypeArrow (subst sigma ty1) (subst sigma ty2)
  subst sigma (TypeForall tvs ty)
    = TypeForall tvs (subst (foldr (unbindSubst . fst) sigma tvs) ty)

matchType :: Type -> Type -> TypeSubst -> TypeSubst
matchType ty1 ty2 = fromMaybe noMatch (matchType' ty1 ty2)
  where
    noMatch = internalError $ "Transformations.CaseCompletion.matchType: " ++
                                showsPrec 11 ty1 " " ++ showsPrec 11 ty2 ""

matchType' :: Type -> Type -> Maybe (TypeSubst -> TypeSubst)
matchType' (TypeVariable tv) ty
  | ty == TypeVariable tv = Just id
  | otherwise = Just (bindSubst tv ty)
matchType' (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
  | tc1 == tc2 = Just $ foldr (\(ty1, ty2) -> (matchType ty1 ty2 .)) id $ tys
  where tys = zip tys1 tys2
matchType' (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
  Just (matchType ty11 ty21 . matchType ty12 ty22)
matchType' _ _ = Nothing
