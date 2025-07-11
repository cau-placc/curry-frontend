{- |
    Module      :  $Header$
    Description :  Translation of Curry into IL
    Copyright   :  (c) 1999 - 2003 Wolfgang Lux
                                   Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2015        Jan Tikovsky
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After desugaring and lifting have been performed, the source code is
   translated into the intermediate language. Besides translating from
   source terms and expressions into intermediate language terms and
   expressions, this phase in particular has to implement the pattern
   matching algorithm for equations and case expressions.

   Because of name conflicts between the source and intermediate language
   data structures, we can use only a qualified import for the 'IL' module.
-}
module Curry.Frontend.Transformations.CurryToIL (ilTrans, transType) where
import           Control.Monad.Extra         (concatMapM)
import           Control.Monad.Reader        (Reader, asks, runReader)
import Control.Monad.State                   (State, put, get, execState)
import           Data.List                   (nub, partition)
import           Data.Maybe                  (fromJust)
import qualified Data.Map             as Map

import Curry.Base.Ident
import Curry.Syntax hiding (caseAlt)

import Curry.Frontend.Base.Expr
import Curry.Frontend.Base.Messages (internalError)
import Curry.Frontend.Base.Types hiding (polyType)
import Curry.Frontend.Base.Kinds
import Curry.Frontend.Base.Typing
import Curry.Frontend.Base.Utils (foldr2)

import Curry.Frontend.Env.TypeConstructor
import Curry.Frontend.Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

import qualified Curry.Frontend.IL as IL

ilTrans :: ValueEnv -> TCEnv -> Module Type -> IL.Module
ilTrans vEnv tcEnv (Module _ _ _ m _ im ds) = IL.Module m (map moduleImport im) ds'
  where ds' = runReader (concatMapM trDecl ds) (TransEnv m vEnv tcEnv)
        moduleImport (ImportDecl _ mdl _ _ _) = mdl

-- -----------------------------------------------------------------------------
-- Internal reader monad
-- -----------------------------------------------------------------------------

data TransEnv = TransEnv
  { moduleIdent :: ModuleIdent
  , valueEnv    :: ValueEnv
  , tyconEnv    :: TCEnv
  }

type TransM a = Reader TransEnv a

getValueEnv :: TransM ValueEnv
getValueEnv = asks valueEnv

getTCEnv :: TransM TCEnv
getTCEnv = asks tyconEnv

trQualify :: Ident -> TransM QualIdent
trQualify i = asks ((`qualifyWith` i) . moduleIdent)

getArity :: QualIdent -> TransM Int
getArity qid = do
    vEnv <- getValueEnv
    return $ case qualLookupValue qid vEnv of
      [DataConstructor  _ a _ _] -> a
      [NewtypeConstructor _ _ _] -> 1
      [Value            _ _ a _] -> a
      [Label              _ _ _] -> 1
      _                          ->
        internalError $ "CurryToIL.getArity: " ++ show qid

-- Return the type of a constructor
constrType :: QualIdent -> TransM Type
constrType c = do
  vEnv <- getValueEnv
  case qualLookupValue c vEnv of
    [DataConstructor  _ _ _ (ForAll _ (PredType _ ty))] -> return ty
    [NewtypeConstructor _ _ (ForAll _ (PredType _ ty))] -> return ty
    _ -> internalError $ "CurryToIL.constrType: " ++ show c

-- Return the kinds of a type constructor's type variables
tcTVarKinds :: QualIdent -> TransM [Kind]
tcTVarKinds qid = do
  tcEnv <- getTCEnv
  let mid = fromJust $ qidModule qid
      kind = tcKind mid qid tcEnv
  return $ kindArgs kind

-- -----------------------------------------------------------------------------
-- Translation
-- -----------------------------------------------------------------------------

-- At the top-level, the compiler has to translate data type, newtype,
-- function, and external declarations. When translating a data type or
-- newtype declaration, we ignore the types in the declaration and lookup
-- the types of the constructors in the type environment instead because
-- these types are already fully expanded, i.e., they do not include any
-- alias types.

trDecl :: Decl Type -> TransM [IL.Decl]
trDecl (DataDecl     _ tc tvs cs _) = (:[]) <$> trData tc tvs cs
trDecl (NewtypeDecl  _ tc tvs nc _) = (:[]) <$> trNewtype tc tvs nc
trDecl (ExternalDataDecl  _ tc tvs) = (:[]) <$> trExternalData tc tvs
trDecl (FunctionDecl    _ _ f  eqs) = (:[]) <$> trFunction f eqs
trDecl (ExternalDecl          _ vs) = mapM trExternal vs
trDecl _                            = return []

trData :: Ident -> [Ident] -> [ConstrDecl] -> TransM IL.Decl
trData tc _ cs = do
  tc' <- trQualify tc
  ks <- tcTVarKinds tc'
  IL.DataDecl tc' (transKind <$> ks) <$> mapM trConstrDecl cs

trNewtype :: Ident -> [Ident] -> NewConstrDecl -> TransM IL.Decl
trNewtype tc _ nc = do
  tc' <- trQualify tc
  ks <- tcTVarKinds tc'
  IL.NewtypeDecl tc' (transKind <$> ks) <$> trNewConstrDecl nc

trConstrDecl :: ConstrDecl -> TransM IL.ConstrDecl
trConstrDecl d = do
  c' <- trQualify (constr d)
  ty' <- arrowArgs <$> constrType c'
  tcEnv <- getTCEnv
  return $ IL.ConstrDecl c' (map (transType tcEnv) ty')
  where
  constr (ConstrDecl    _ c _) = c
  constr (ConOpDecl  _ _ op _) = op
  constr (RecordDecl    _ c _) = c

trNewConstrDecl :: NewConstrDecl -> TransM IL.NewConstrDecl
trNewConstrDecl d = do
  c' <- trQualify (constr d)
  ty' <- arrowArgs <$> constrType c'
  tcEnv <- getTCEnv
  case ty' of
    [ty] -> return $ IL.NewConstrDecl c' (transType tcEnv ty)
    _    -> internalError "CurryToIL.trNewConstrDecl: invalid constructor type"
  where
  constr (NewConstrDecl    _ c _) = c
  constr (NewRecordDecl    _ c _) = c

trExternalData :: Ident -> [Ident] -> TransM IL.Decl
trExternalData tc _ = do
  tc' <- trQualify tc
  ks <- tcTVarKinds tc'
  return $ IL.ExternalDataDecl tc' (transKind <$> ks)

trExternal :: Var Type -> TransM IL.Decl
trExternal (Var ty f) = do
  tcEnv <- getTCEnv
  f' <- trQualify f
  a <- getArity f'
  return $ IL.ExternalDecl f' a (transType tcEnv $ polyType ty)

-- The type representation in the intermediate language does not support
-- types with higher order kinds. Therefore, the type transformations has
-- to transform all types to first order terms. To that end, we assume the
-- existence of a type synonym 'type Apply f a = f a'. In addition, the type
-- representation of the intermediate language does not support constrained
-- type variables and skolem types. The former are fixed and the later are
-- replaced by fresh type constructors.

transType :: TCEnv -> Type -> IL.Type
transType tcEnv ty' = transType' ty' []
  where
    ks = transTVars tcEnv ty'
    transType' (TypeConstructor    tc) = IL.TypeConstructor tc
    transType' (TypeApply     ty1 ty2) = transType' ty1 . (transType' ty2 [] :)
    transType' (TypeVariable       tv) = foldl applyType' (IL.TypeVariable tv)
    transType' (TypeConstrained tys _) = transType' (head tys)
    transType' (TypeArrow     ty1 ty2) =
      foldl applyType' (IL.TypeArrow (transType' ty1 []) (transType' ty2 []))
    transType' (TypeForall     tvs ty) =
      foldl applyType' (IL.TypeForall tvs' (transType' ty []))
      where tvs' = filter ((`elem` tvs) . fst) ks

applyType' :: IL.Type -> IL.Type -> IL.Type
applyType' ty1 ty2 =
  IL.TypeConstructor (qualifyWith preludeMIdent (mkIdent "Apply")) [ty1, ty2]

-- We need to existentially quantify all variables in some types
polyType :: Type -> Type
polyType (TypeForall _ ty) = polyType ty
polyType ty                =
  let vs = nub $ typeVars ty
  in if null vs then ty else TypeForall vs ty

-- We need to infer kinds for the quantified variables.
-- We already checked the correctness of all Kinds earlier,
-- thus we know that we will be able to unify all the inferred equations.
-- We can also keep a flat environment,
-- as all variables have already been renamed.

data KIS = KIS
  { _nextKindId :: Int
  , kinds  :: Map.Map Int IL.Kind
  }

freshKindId :: State KIS Int
freshKindId = do
  KIS i ks <- get
  put (KIS (i+1) ks)
  return i

transTVars :: TCEnv -> Type -> [(Int, IL.Kind)]
transTVars tcEnv ty' =
  Map.toList $ kinds $ execState (build ty' IL.KindStar) (KIS 0 Map.empty)
  where
    build :: Type -> IL.Kind -> State KIS ()
    build (TypeArrow     ty1 ty2) _ =
      build ty1 IL.KindStar >> build ty2 IL.KindStar
    build (TypeConstrained tys _) k =
      build (head tys) k
    build (TypeForall       _ ty) k =
      build ty k
    build (TypeVariable       tv) k = do
      KIS i ks <- get
      -- get current kind
      let k' = Map.findWithDefault k tv ks
      -- unify it
      let s = unifyKind k k'
      -- apply substitution
      let ks' = applyKindSubst s <$> Map.insert tv k' ks
      put (KIS i ks')
    build (TypeConstructor     _) _ = return ()
    build ta@(TypeApply       _ _) k =
      let (ty, tys) = unapplyType True ta
      in case ty of
        TypeConstructor tc -> do
          let k' = tcKind (fromJust $ qidModule tc) tc tcEnv
          mapM_ (uncurry build) (zip tys $ unarrowKind $ transKind k')
        _ -> do -- var of forall
          -- construct new kind vars
          ks <- mapM (const (IL.KindVariable <$> freshKindId)) tys
          -- infer kind for v
          build ty (foldr IL.KindArrow k ks)
          -- infer kinds for args
          mapM_ (uncurry build) (zip tys ks)

type KindSubst = Map.Map Int IL.Kind

transKind :: Kind -> IL.Kind
transKind KindStar          = IL.KindStar
transKind KindConstraint    = internalError $ "CurryToIL.transKind: " ++
                                "Encountered untransformed constraint kind"
transKind (KindVariable  _) = IL.KindStar
transKind (KindArrow k1 k2) = IL.KindArrow (transKind k1) (transKind k2)

unarrowKind :: IL.Kind -> [IL.Kind]
unarrowKind (IL.KindArrow k1 k2) = k1 : unarrowKind k2
unarrowKind k                    = [k]

applyKindSubst :: KindSubst -> IL.Kind -> IL.Kind
applyKindSubst _ IL.KindStar =
  IL.KindStar
applyKindSubst s (IL.KindArrow k1 k2) =
  IL.KindArrow (applyKindSubst s k1) (applyKindSubst s k2)
applyKindSubst s v@(IL.KindVariable i) =
  Map.findWithDefault v i s

composeKindSubst :: KindSubst -> KindSubst -> KindSubst
composeKindSubst s1 s2 = Map.map (applyKindSubst s1) s2 `Map.union` s1

unifyKind :: IL.Kind -> IL.Kind -> KindSubst
unifyKind IL.KindStar          IL.KindStar            = Map.empty
unifyKind (IL.KindVariable i)  k                      = Map.singleton i k
unifyKind k                    (IL.KindVariable i)    = Map.singleton i k
unifyKind (IL.KindArrow k1 k2) (IL.KindArrow k1' k2') =
  let s1 = unifyKind k1 k1'
      s2 = unifyKind (applyKindSubst s1 k2) (applyKindSubst s1 k2')
  in s1 `composeKindSubst` s2
unifyKind k1 k2 = error $ "Transformation.CurryToIL.unifyKind: " ++ show k1 ++ ", " ++ show k2

-- Each function in the program is translated into a function of the
-- intermediate language. The arguments of the function are renamed such
-- that all variables occurring in the same position (in different
-- equations) have the same name. This is necessary in order to
-- facilitate the translation of pattern matching into a 'case' expression.
-- We use the following simple convention here: The top-level
-- arguments of the function are named from left to right '_1', '_2',
-- and so on. The names of nested arguments are constructed by appending
-- '_1', '_2', etc. from left to right to the name that were assigned
-- to a variable occurring at the position of the constructor term.

-- Some special care is needed for the selector functions introduced by
-- the compiler in place of pattern bindings. In order to generate the
-- code for updating all pattern variables, the equality of names between
-- the pattern variables in the first argument of the selector function
-- and their repeated occurrences in the remaining arguments must be
-- preserved. This means that the second and following arguments of a
-- selector function have to be renamed according to the name mapping
-- computed for its first argument.

trFunction :: Ident -> [Equation Type] -> TransM IL.Decl
trFunction f eqs = do
  f' <- trQualify f
  tcEnv <- getTCEnv
  let tys = map typeOf ts
      ty' = transType tcEnv $ polyType $ foldr TypeArrow (typeOf rhs) tys
      vs' = zip (map (transType tcEnv) tys) vs
  alts <- mapM (trEquation vs ws) eqs
  return $ IL.FunctionDecl f' vs' ty' (flexMatch vs' alts)
  where
  -- vs are the variables needed for the function: _1, _2, etc.
  -- ws is an infinite list for introducing additional variables later
  Equation _ _ lhs rhs = head eqs
  (_, ts) = flatLhs lhs
  (vs, ws) = splitAt (length ts) (argNames (mkIdent ""))

trEquation :: [Ident]       -- identifiers for the function's parameters
           -> [Ident]       -- infinite list of additional identifiers
           -> Equation Type -- equation to be translated
           -> TransM Match  -- nested constructor terms + translated RHS
trEquation vs vs' (Equation _ _ (FunLhs _ _ ts) rhs) = do
  -- construct renaming of variables inside constructor terms
  let patternRenaming = foldr2 bindRenameEnv Map.empty vs ts
  -- translate right-hand-side
  rhs' <- trRhs vs' patternRenaming rhs
  -- convert patterns
  tcEnv <- getTCEnv
  return (zipWith (trPattern tcEnv) vs ts, rhs')
trEquation _  _    _
  = internalError "Translation of non-FunLhs euqation not defined"

type RenameEnv = Map.Map Ident Ident

-- Construct a renaming of all variables inside the pattern to fresh identifiers
bindRenameEnv :: Ident -> Pattern a -> RenameEnv -> RenameEnv
bindRenameEnv _ (LiteralPattern        _ _ _) env = env
bindRenameEnv v (VariablePattern      _ _ v') env = Map.insert v' v env
bindRenameEnv v (ConstructorPattern _ _ _ ts) env
  = foldr2 bindRenameEnv env (argNames v) ts
bindRenameEnv v (AsPattern            _ v' t) env
  = Map.insert v' v (bindRenameEnv v t env)
bindRenameEnv _ _                           _
  = internalError "CurryToIL.bindRenameEnv"

trRhs :: [Ident] -> RenameEnv -> Rhs Type -> TransM IL.Expression
trRhs vs env (SimpleRhs _ _ e _) = trExpr vs env e
trRhs _  _   (GuardedRhs {})     = internalError "CurryToIL.trRhs: GuardedRhs"

-- Note that the case matching algorithm assumes that the matched
-- expression is accessible through a variable. The translation of case
-- expressions therefore introduces a let binding for the scrutinized
-- expression and immediately throws it away after the matching -- except
-- if the matching algorithm has decided to use that variable in the
-- right hand sides of the case expression. This may happen, for
-- instance, if one of the alternatives contains an as-pattern.

trExpr :: [Ident] -> RenameEnv -> Expression Type -> TransM IL.Expression
trExpr _  _   (Literal     _ ty l) = do
  tcEnv <- getTCEnv
  return $ IL.Literal (transType tcEnv ty) (trLiteral l)
trExpr _  env (Variable    _ ty v)
  | isQualified v = getTCEnv >>= fun
  | otherwise     = do
    tcEnv <- getTCEnv
    case Map.lookup (unqualify v) env of
      Nothing -> error $ "unexpected variable" ++ show v
      Just v' -> return $ IL.Variable (transType tcEnv ty) v' -- apply renaming
  where
    fun tcEnv = IL.Function (transType tcEnv ty) v <$> getArity v
trExpr _  _   (Constructor _ ty c) = do
  tcEnv <- getTCEnv
  IL.Constructor (transType tcEnv ty) c <$> getArity c
trExpr vs env (Apply     _ e1 e2)
  = IL.Apply <$> trExpr vs env e1 <*> trExpr vs env e2
trExpr vs env (Let      _ _ ds e) = do
  e' <- trExpr vs env' e
  case ds of
    [FreeDecl _ vs']
       -> do tcEnv <- getTCEnv
             return $
               foldr (\ (Var ty v) -> IL.Exist v (transType tcEnv ty)) e' vs'
    [d] | all (`notElem` bv d) (qfv emptyMIdent d)
      -> flip IL.Let    e' <$>      trBinding d
    _ -> flip IL.Letrec e' <$> mapM trBinding ds
  where
  env' = foldr2 Map.insert env bvs bvs
  bvs  = bv ds
  trBinding (PatternDecl _ (VariablePattern _ _ v) rhs)
    = IL.Binding v <$> trRhs vs env' rhs
  trBinding p = error $ "unexpected binding: " ++ show p
trExpr (v:vs) env (Case _ _ ct e alts) = do
  -- the ident v is used for the case expression subject, as this could
  -- be referenced in the case alternatives by a variable pattern
  e' <- trExpr vs env e
  tcEnv <- getTCEnv
  let matcher = if ct == Flex then flexMatch else rigidMatch
      ty'     = transType tcEnv $ typeOf e
  expr <-  matcher [(ty', v)] <$> mapM (trAlt v vs env) alts
  return $ case expr of
    IL.Case mode (IL.Variable _ v') alts'
        -- subject is not referenced -> forget v and insert subject
      | v == v' && v `notElem` fv alts' -> IL.Case mode e' alts'
    _
        -- subject is referenced -> introduce binding for v as subject
      | v `elem` fv expr                -> IL.Let (IL.Binding v e') expr
      | otherwise                       -> expr
trExpr vs env (Typed _ e _) = do
  tcEnv <- getTCEnv
  e' <- trExpr vs env e
  return $ IL.Typed e' (transType tcEnv $ typeOf e)
trExpr _ _ _ = internalError "CurryToIL.trExpr"

trAlt :: Ident -> [Ident] -> RenameEnv -> Alt Type -> TransM Match
trAlt v vs env (Alt _ t rhs) = do
  tcEnv <- getTCEnv
  rhs' <- trRhs vs (bindRenameEnv v t env) rhs
  return ([trPattern tcEnv v t], rhs')

trLiteral :: Literal -> IL.Literal
trLiteral (Char  c) = IL.Char c
trLiteral (Int   i) = IL.Int i
trLiteral (Float f) = IL.Float f
trLiteral (String s) = IL.String s

-- -----------------------------------------------------------------------------
-- Translation of Patterns
-- -----------------------------------------------------------------------------

data NestedTerm = NestedTerm IL.ConstrTerm [NestedTerm] deriving Show

getPattern :: NestedTerm -> IL.ConstrTerm
getPattern (NestedTerm t _) = t

arguments :: NestedTerm -> [NestedTerm]
arguments (NestedTerm _ ts) = ts

trPattern :: TCEnv -> Ident -> Pattern Type -> NestedTerm
trPattern tcEnv _ (LiteralPattern        _ ty l)
  = NestedTerm (IL.LiteralPattern (transType tcEnv ty) $ trLiteral l) []
trPattern tcEnv v (VariablePattern       _ ty _)
  = NestedTerm (IL.VariablePattern (transType tcEnv ty) v) []
trPattern tcEnv v (ConstructorPattern _ ty c ts)
  = NestedTerm (IL.ConstructorPattern (transType tcEnv ty) c vs')
               (zipWith (trPattern tcEnv) vs ts)
  where vs  = argNames v
        vs' = zip (map (transType tcEnv . typeOf) ts) vs
trPattern tcEnv v (AsPattern              _ _ t)
  = trPattern tcEnv v t
trPattern _ _ _
  = internalError "CurryToIL.trPattern"

argNames :: Ident -> [Ident]
argNames v = [mkIdent (prefix ++ show i) | i <- [1 :: Integer ..] ]
  where prefix = idName v ++ "_"

-- -----------------------------------------------------------------------------
-- Flexible Pattern Matching Algorithm
-- -----------------------------------------------------------------------------

-- The pattern matching code searches for the left-most inductive
-- argument position in the left hand sides of all rules defining an
-- equation. An inductive position is a position where all rules have a
-- constructor rooted term. If such a position is found, a flexible 'case'
-- expression is generated for the argument at that position. The
-- matching code is then computed recursively for all of the alternatives
-- independently. If no inductive position is found, the algorithm looks
-- for the left-most demanded argument position, i.e., a position where
-- at least one of the rules has a constructor rooted term. If such a
-- position is found, an 'or' expression is generated with those
-- cases that have a variable at the argument position in one branch and
-- all other rules in the other branch. If there is no demanded position,
-- the pattern matching is finished and the compiler translates the right
-- hand sides of the remaining rules, eventually combining them using
-- 'or' expressions.

-- Actually, the algorithm below combines the search for inductive and
-- demanded positions. The function 'flexMatch' scans the argument
-- lists for the left-most demanded position. If this turns out to be
-- also an inductive position, the function 'flexMatchInductive' is
-- called in order to generate a flexible 'case' expression. Otherwise, the
-- function 'optFlexMatch' is called that tries to find an inductive
-- position in the remaining arguments. If one is found,
-- 'flexMatchInductive' is called, otherwise the function
-- 'optFlexMatch' uses the demanded argument position found by 'flexMatch'.

-- a @Match@ is a list of patterns and the respective expression.
type Match  = ([NestedTerm], IL.Expression)
-- a @Match'@ is a @Match@ with skipped patterns during the search for an
-- inductive position.
type Match' = (FunList NestedTerm, [NestedTerm], IL.Expression)
-- Functional lists
type FunList a = [a] -> [a]

flexMatch :: [(IL.Type, Ident)] -- variables to be matched
          -> [Match]            -- alternatives
          -> IL.Expression      -- result expression
flexMatch []     alts = foldl1 IL.Or (map snd alts)
flexMatch (v:vs) alts
  | notDemanded = varExp
  | isInductive = conExp
  | otherwise   = optFlexMatch (IL.Or conExp varExp) (v:) vs (map skipPat alts)
  where
  isInductive        = null varAlts
  notDemanded        = null conAlts
  -- separate variable and constructor patterns
  (varAlts, conAlts) = partition isVarMatch (map tagAlt alts)
  -- match variables
  varExp             = flexMatch               vs (map snd  varAlts)
  -- match constructors
  conExp             = flexMatchInductive id v vs (map prep conAlts)
  prep (p, (ts, e))  = (p, (id, ts, e))

-- Search for the next inductive position
optFlexMatch :: IL.Expression            -- default expression
             -> FunList (IL.Type, Ident) -- skipped variables
             -> [(IL.Type, Ident)]       -- next variables
             -> [Match']                 -- alternatives
             -> IL.Expression
optFlexMatch def _      []     _    = def
optFlexMatch def prefix (v:vs) alts
  | isInductive = flexMatchInductive prefix v vs alts'
  | otherwise   = optFlexMatch def (prefix . (v:)) vs (map skipPat' alts)
  where
  isInductive   = not (any isVarMatch alts')
  alts'         = map tagAlt' alts

-- Generate a case expression matching the inductive position
flexMatchInductive :: FunList (IL.Type, Ident)  -- skipped variables
                   -> (IL.Type, Ident)          -- current variable
                   -> [(IL.Type, Ident)]        -- next variables
                   -> [(IL.ConstrTerm, Match')] -- alternatives
                   -> IL.Expression
flexMatchInductive prefix v vs as'
  = IL.Case IL.Flex (uncurry IL.Variable v) (flexMatchAlts as)
  where
  as = map (desugarOuterLit (snd v)) as'
  -- create alternatives for the different constructors
  flexMatchAlts []              = []
  flexMatchAlts ((t, e) : alts) = IL.Alt t expr : flexMatchAlts others
    where
    -- match nested patterns for same constructors
    expr = flexMatch (prefix (vars t ++ vs)) (map expandVars (e : map snd same))
    expandVars (pref, ts1, e') = (pref ts1, e')
    -- split into same and other constructors
    (same, others) = partition ((t ==) . fst) alts

-- -----------------------------------------------------------------------------
-- Rigid Pattern Matching Algorithm
-- -----------------------------------------------------------------------------

-- Matching in a 'case'-expression works a little bit differently.
-- In this case, the alternatives are matched from the first to the last
-- alternative and the first matching alternative is chosen. All
-- remaining alternatives are discarded.

-- TODO: The case matching algorithm should use type information in order
-- to detect total matches and immediately discard all alternatives which
-- cannot be reached.

rigidMatch :: [(IL.Type, Ident)] -> [Match] -> IL.Expression
rigidMatch vs alts = rigidOptMatch (snd $ head alts) id vs (map prepare alts)
  where prepare (ts, e) = (id, ts, e)

rigidOptMatch :: IL.Expression            -- default expression
              -> FunList (IL.Type, Ident) -- variables to be matched next
              -> [(IL.Type, Ident)]       -- variables to be matched afterwards
              -> [Match']                 -- translated equations
              -> IL.Expression
-- if there are no variables left: return the default expression
rigidOptMatch def _      []       _    = def
rigidOptMatch def prefix (v : vs) alts
  | isDemanded = rigidMatchDemanded prefix v vs alts'
  | otherwise  = rigidOptMatch def (prefix . (v:)) vs (map skipPat' alts)
  where
  isDemanded   = not $ isVarMatch (head alts')
  alts'        = map tagAlt' alts

-- Generate a case expression matching the demanded position.
-- This algorithm constructs a branch for all contained patterns, where
-- the right-hand side then respects the order of the patterns.
-- Thus, the expression
--    case x of
--      []   -> []
--      ys   -> ys
--      y:ys -> [y]
-- gets translated to
--    case x of
--      []   -> []
--      y:ys -> x
--      x    -> x
rigidMatchDemanded :: FunList (IL.Type, Ident)  -- skipped variables
                   -> (IL.Type, Ident)          -- current variable
                   -> [(IL.Type, Ident)]        -- next variables
                   -> [(IL.ConstrTerm, Match')] -- alternatives
                   -> IL.Expression
rigidMatchDemanded prefix v vs alts' =
  IL.Case IL.Rigid (uncurry IL.Variable v) $ map caseAlt (consPats ++ varPats)
  where
    alts = handleMixedLiteralPatterns (snd v) alts'
    -- N.B.: @varPats@ is either empty or a singleton list due to nub
    -- This relies on the uniform naming scheme for variables
    (varPats, consPats) = partition isVarPattern $ nub $ map fst alts
    caseAlt t           = IL.Alt t expr
      where
      expr = rigidMatch (prefix $ vars t ++ vs) (matchingCases alts)
      -- matchingCases selects the matching alternatives
      --  and recursively matches the remaining patterns
      matchingCases a = map (expandVars (vars t)) $ filter (matches . fst) a
      matches t' = t == t' || isVarPattern t'
      expandVars vs' (p, (pref, ts1, e)) = (pref ts2, e)
        where ts2 | isVarPattern p = map var2Pattern vs' ++ ts1
                  | otherwise      = ts1
              var2Pattern v' = NestedTerm (uncurry IL.VariablePattern v') []

-- It might still happen that there are string and list constructor pattern mixed in the same pattern position
-- Consider the following example:
-- case _1 of
--   'v':_ -> 1
--   "-f"  -> 2
--   "-g"  -> 3
--   s     -> 4
-- The function @handleMixedLiteralPatterns@ detects these cases
-- and processes them with @desugarOuterLit@ if required.
-- The latter just transforms the first character of each string literal into a `(:)` match
-- with the character and remaining string literal pattern added as a nested to-be-matched term.
-- It is imperative that the variables created as the arguments to the `(:)` match
-- are correctly named for the current level.
-- Thus, we pass in the previous identified name and add a "_1"/"_2" suffix.
-- Also note that this only works because cases are flat.
-- The following characters of a string literal might thus be desugared later.
handleMixedLiteralPatterns :: Ident -> [(IL.ConstrTerm, Match')] -> [(IL.ConstrTerm, Match')]
handleMixedLiteralPatterns idt alts =
  if any (isLiteralPattern . fst) alts && any (isConstructorPattern . fst) alts
    -- can only be a string, because other primitives do not have constructors
    then map (desugarOuterLit idt) alts
    else alts

desugarOuterLit :: Ident -> (IL.ConstrTerm, Match') -> (IL.ConstrTerm, Match')
desugarOuterLit _ (IL.LiteralPattern listTy (IL.String ""), (pref, ts, e)) =
  (IL.ConstructorPattern listTy qNilId [], (pref, ts, e))
desugarOuterLit idt (IL.LiteralPattern listTy (IL.String (c:s)), (pref, ts, e)) =
  let charTy = IL.TypeConstructor qCharId []
      p1 = (charTy, idt { idName = idName idt ++ "_1" })
      p2 = (listTy, idt { idName = idName idt ++ "_2" })
      n1 = NestedTerm (IL.LiteralPattern charTy (IL.Char c)) []
      n2 = NestedTerm (IL.LiteralPattern listTy (IL.String s)) []
  in (IL.ConstructorPattern listTy qConsId [p1, p2], (pref, [n1, n2] ++ ts, e))
desugarOuterLit _ m = m

-- -----------------------------------------------------------------------------
-- Pattern Matching Auxiliaries
-- -----------------------------------------------------------------------------

isVarPattern :: IL.ConstrTerm -> Bool
isVarPattern (IL.VariablePattern _ _) = True
isVarPattern _                        = False

isLiteralPattern :: IL.ConstrTerm -> Bool
isLiteralPattern (IL.LiteralPattern _ _) = True
isLiteralPattern _                       = False

isConstructorPattern :: IL.ConstrTerm -> Bool
isConstructorPattern (IL.ConstructorPattern {}) = True
isConstructorPattern _                          = False

isVarMatch :: (IL.ConstrTerm, a) -> Bool
isVarMatch = isVarPattern . fst

vars :: IL.ConstrTerm -> [(IL.Type, Ident)]
vars (IL.ConstructorPattern _ _ vs) = vs
vars _                              = []

-- tagAlt extracts the structure of the first pattern
tagAlt :: Match -> (IL.ConstrTerm, Match)
tagAlt (t:ts, e) = (getPattern t, (arguments t ++ ts, e))
tagAlt ([]  , _) = error "CurryToIL.tagAlt: empty pattern list"

-- skipPat skips the current pattern position for later matching
skipPat :: Match -> Match'
skipPat (t:ts, e) = ((t:), ts, e)
skipPat ([]  , _) = error "CurryToIL.skipPat: empty pattern list"

-- tagAlt' extracts the next pattern
tagAlt' :: Match' -> (IL.ConstrTerm, Match')
tagAlt' (pref, t:ts, e') = (getPattern t, (pref, arguments t ++ ts, e'))
tagAlt' (_   , []  , _ ) = error "CurryToIL.tagAlt': empty pattern list"

-- skipPat' skips the current argument for later matching
skipPat' :: Match' -> Match'
skipPat' (pref, t:ts, e') = (pref . (t:), ts, e')
skipPat' (_   , []  , _ ) = error "CurryToIL.skipPat': empty pattern list"
