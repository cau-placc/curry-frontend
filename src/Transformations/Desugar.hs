{- |
  Module      :  $Header$
  Description :  Desugaring Curry Expressions
  Copyright   :  (c) 2001 - 2004 Wolfgang Lux
                                 Martin Engelke
                     2011 - 2015 Björn Peemöller
                     2015        Jan Tikovsky
                     2016 - 2017 Finn Teegen
  License     :  BSD-3-clause

  Maintainer  :  bjp@informatik.uni-kiel.de
  Stability   :  experimental
  Portability :  portable

  The desugaring pass removes all syntactic sugar from the module.
  In particular, the output of the desugarer will have the following
  properties.

  * No guarded right hand sides occur in equations, pattern declarations,
    and case alternatives. In addition, the declaration lists (`where`-blocks)
    of the right hand sides are empty; local declarations are transformed
    into let expressions.

  * Patterns in equations and case alternatives are composed only of
    - literals,
    - variables,
    - constructor applications, and
    - as patterns applied to literals or constructor applications.

  * Expressions are composed only of
    - literals,
    - variables,
    - constructors,
    - (binary) applications,
    - case expressions,
    - let expressions, and
    - expressions with a type signature.

  * Functional patterns are replaced by variables and are integrated
    in a guarded right hand side using the (=:<=) operator.

  * Records are transformed into ordinary data types by removing the fields.
    Record construction and pattern matching are represented using solely the
    record constructor. Record selections are represented using selector
    functions which are generated for each record declaration, and record
    updated are represented using case-expressions that perform the update.

  * The type environment will be extended by new function declarations for:
    - Record selections, and
    - Converted lambda expressions.

  As we are going to insert references to real prelude entities,
  all names must be properly qualified before calling this module.
-}
{-# LANGUAGE CPP #-}
module Transformations.Desugar (desugar) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Arrow              (first, second)
import           Control.Monad              (liftM2)
import           Control.Monad.Extra        (concatMapM)
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.Foldable              (foldrM)
import           Data.List                  ( (\\), elemIndex, nub, partition
                                            , tails )
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set (Set, empty, member, insert)

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax

import Base.Expr
import Base.CurryTypes
import Base.Messages (internalError)
import Base.TypeExpansion
import Base.Types
import Base.TypeSubst
import Base.Typing
import Base.Utils (fst3, mapAccumM)
import Base.Linearity

import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTypeInfo)
import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

-- TODO: some types keep their spanInfo, some don't. Probably none of them are needed

-- The desugaring phase keeps only the type, function, and value
-- declarations of the module, i.e., type signatures are discarded.
-- While record declarations are transformed into ordinary data/newtype
-- declarations, the remaining type declarations are not desugared.
-- Since they cannot occur in local declaration groups, they are filtered
-- out separately. Actually, the transformation is slightly more general than
-- necessary as it allows value declarations at the top-level of a module.

desugar :: [KnownExtension] -> ValueEnv -> TCEnv -> Module PredType
        -> (Module PredType, ValueEnv)
desugar xs vEnv tcEnv (Module spi ps m es is ds)
  = (Module spi ps m es is ds', valueEnv s')
  where (ds', s') = S.runState (desugarModuleDecls ds)
                               (DesugarState m xs tcEnv vEnv 1 ds)

-- ---------------------------------------------------------------------------
-- Desugaring monad and accessor functions
-- ---------------------------------------------------------------------------

-- New identifiers may be introduced while desugaring pattern declarations,
-- case and lambda-expressions, list comprehensions, and record selections
-- and updates. As usual, we use a state monad transformer for generating
-- unique names. In addition, the state is also used for passing through the
-- type environment, which must be augmented with the types of these new
-- variables.

data DesugarState = DesugarState
  { moduleIdent :: ModuleIdent      -- read-only
  , extensions  :: [KnownExtension] -- read-only
  , tyConsEnv   :: TCEnv            -- read-only
  , valueEnv    :: ValueEnv         -- will be extended
  , nextId      :: Integer          -- counter
  , allDecls    :: [Decl PredType]
  }

type DsM a = S.State DesugarState a

getModuleIdent :: DsM ModuleIdent
getModuleIdent = S.gets moduleIdent

checkNegativeLitsExtension :: DsM Bool
checkNegativeLitsExtension = S.gets (\s -> NegativeLiterals `elem` extensions s)

getTyConsEnv :: DsM TCEnv
getTyConsEnv = S.gets tyConsEnv

getValueEnv :: DsM ValueEnv
getValueEnv = S.gets valueEnv

getNextId :: DsM Integer
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

-- ---------------------------------------------------------------------------
-- Generation of fresh names
-- ---------------------------------------------------------------------------

-- Create a fresh variable ident for a given prefix with a monomorphic type
freshVar :: Typeable t => String -> t -> DsM (PredType, Ident)
freshVar prefix t = do
  v <- (mkIdent . (prefix ++) . show) <$> getNextId
  return (predType $ typeOf t, v)

-- ---------------------------------------------------------------------------
-- Desugaring
-- ---------------------------------------------------------------------------

desugarModuleDecls :: [Decl PredType] -> DsM [Decl PredType]
desugarModuleDecls ds = do
  ds'   <- concatMapM dsRecordDecl ds
  ds''  <- mapM dsClassAndInstanceDecl ds'
  ds''' <- dsDeclGroup ds''
  return $ filter (not . liftM2 (||) isValueDecl isTypeSig) ds'' ++ ds'''

-- -----------------------------------------------------------------------------
-- Desugaring of class and instance declarations
-- -----------------------------------------------------------------------------

dsClassAndInstanceDecl :: Decl PredType -> DsM (Decl PredType)
dsClassAndInstanceDecl (ClassDecl p cx cls tv ds) =
  ClassDecl p cx cls tv . (tds ++) <$> dsDeclGroup vds
  where (tds, vds) = partition isTypeSig ds
dsClassAndInstanceDecl (InstanceDecl p cx cls ty ds) =
  InstanceDecl p cx cls ty <$> dsDeclGroup ds
dsClassAndInstanceDecl d = return d

-- -----------------------------------------------------------------------------
-- Desugaring of type declarations: records
-- -----------------------------------------------------------------------------

-- As an extension to the Curry language, the compiler supports Haskell's
-- record syntax, which introduces field labels for data and renaming types.
-- Field labels can be used in constructor declarations, patterns,
-- and expressions. For further convenience, an implicit selector
-- function is introduced for each field label.

-- Generate selector functions for record labels and replace record
-- constructor declarations by ordinary constructor declarations.
dsRecordDecl :: Decl PredType -> DsM [Decl PredType]
dsRecordDecl (DataDecl p tc tvs cs clss) = do
  m <- getModuleIdent
  let qcs = map (qualifyWith m . constrId) cs
  selFuns <- mapM (genSelFun p qcs) (nub $ concatMap recordLabels cs)
  return $ DataDecl p tc tvs (map unlabelConstr cs) clss : selFuns
dsRecordDecl (NewtypeDecl p tc tvs nc clss) = do
  m <- getModuleIdent
  let qc = qualifyWith m (nconstrId nc)
  selFun <- mapM (genSelFun p [qc]) (nrecordLabels nc)
  return $ NewtypeDecl p tc tvs (unlabelNewConstr nc) clss : selFun
dsRecordDecl d = return [d]

-- Generate a selector function for a single record label
genSelFun :: SpanInfo -> [QualIdent] -> Ident -> DsM (Decl PredType)
genSelFun p qcs l = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  let ForAll _ pty = varType (qualifyWith m l) vEnv
  FunctionDecl p pty l <$> concatMapM (genSelEqn p l) qcs

-- Generate a selector equation for a label and a constructor if the label
-- is applicable, otherwise the empty list is returned.
genSelEqn :: SpanInfo -> Ident -> QualIdent -> DsM [Equation PredType]
genSelEqn p l qc = do
  vEnv <- getValueEnv
  let (ls, ty) = conType qc vEnv
      (tys, ty0) = arrowUnapply (instType ty)
  case elemIndex l ls of
    Just n  -> do
      vs <- mapM (freshVar "_#rec") tys
      let pat = constrPattern (predType ty0) qc vs
      return [mkEquation p l [pat] (uncurry mkVar (vs !! n))]
    Nothing -> return []

-- Remove any labels from a data constructor declaration
unlabelConstr :: ConstrDecl -> ConstrDecl
unlabelConstr (RecordDecl p c fs) = ConstrDecl p c tys
  where tys = [ty | FieldDecl _ ls ty <- fs, _ <- ls]
unlabelConstr c                   = c

-- Remove any labels from a newtype constructor declaration
unlabelNewConstr :: NewConstrDecl -> NewConstrDecl
unlabelNewConstr (NewRecordDecl p nc (_, ty)) = NewConstrDecl p nc ty
unlabelNewConstr c                            = c

-- -----------------------------------------------------------------------------
-- Desugaring of value declarations
-- -----------------------------------------------------------------------------

-- Within a declaration group, all type signatures are discarded. First,
-- the patterns occurring in the left hand sides of pattern declarations
-- and external declarations are desugared. Due to lazy patterns, the former
-- may add further declarations to the group that must be desugared as well.
dsDeclGroup :: [Decl PredType] -> DsM [Decl PredType]
dsDeclGroup ds = concatMapM dsDeclLhs (filter isValueDecl ds) >>= mapM dsDeclRhs

dsDeclLhs :: Decl PredType -> DsM [Decl PredType]
dsDeclLhs (PatternDecl p t rhs) = do
  (ds', t') <- dsPat p [] t
  dss'      <- mapM dsDeclLhs ds'
  return $ PatternDecl p t' rhs : concat dss'
dsDeclLhs d                     = return [d]

-- TODO: Check if obsolete and remove
-- After desugaring its right hand side, each equation is eta-expanded
-- by adding as many variables as necessary to the argument list and
-- applying the right hand side to those variables (Note: eta-expansion
-- is disabled in the version for PAKCS).
-- Furthermore every occurrence of a record type within the type of a function
-- is simplified to the corresponding type constructor from the record
-- declaration. This is possible because currently records must not be empty
-- and a record label belongs to only one record declaration.

-- Desugaring of the right-hand-side of declarations
dsDeclRhs :: Decl PredType -> DsM (Decl PredType)
dsDeclRhs (FunctionDecl p pty f eqs) =
  FunctionDecl p pty f <$> mapM dsEquation eqs
dsDeclRhs (PatternDecl      p t rhs) = PatternDecl p t <$> dsRhs id rhs
dsDeclRhs d@(FreeDecl           _ _) = return d
dsDeclRhs d@(ExternalDecl       _ _) = return d
dsDeclRhs _                          =
  error "Desugar.dsDeclRhs: no pattern match"

-- Desugaring of an equation
dsEquation :: Equation PredType -> DsM (Equation PredType)
dsEquation (Equation p lhs rhs) = do
  (     cs1,     ts1) <- dsNonLinearity         ts
  (ds1, fConstr, ts2) <- dsFunctionalPatterns p ts1
  (ds2,          ts3) <- mapAccumM (dsPat p) [] ts2
  rhs'                <- dsRhs (fConstr . constrain cs1)
                               (addDecls (ds1 ++ ds2) rhs)
  return $ Equation p (FunLhs NoSpanInfo f ts3) rhs'
  where (f, ts) = flatLhs lhs

-- Constrain an expression by a list of constraints.
-- @constrain []  e  ==  e@
-- @constrain c_n e  ==  (c_1 & ... & c_n) &> e@
constrain :: [Expression PredType] -> Expression PredType -> Expression PredType
constrain cs e = if null cs then e else foldr1 (&) cs &> e

-- -----------------------------------------------------------------------------
-- Desugaring of right-hand sides
-- -----------------------------------------------------------------------------

-- A list of boolean guards is expanded into a nested if-then-else
-- expression, whereas a constraint guard is replaced by a case
-- expression. Note that if the guard type is 'Success' only a
-- single guard is allowed for each equation (This change was
-- introduced in version 0.8 of the Curry report.). We check for the
-- type 'Bool' of the guard because the guard's type defaults to
-- 'Success' if it is not restricted by the guard expression.

dsRhs :: (Expression PredType -> Expression PredType)
      -> Rhs PredType -> DsM (Rhs PredType)
dsRhs f rhs =   expandRhs (prelFailed (typeOf rhs)) f rhs
            >>= dsExpr (getSpanInfo rhs)
            >>= return . simpleRhs (getSpanInfo rhs)

expandRhs :: Expression PredType -> (Expression PredType -> Expression PredType)
          -> Rhs PredType -> DsM (Expression PredType)
expandRhs _  f (SimpleRhs _ e ds) = return $ Let NoSpanInfo ds (f e)
expandRhs e0 f (GuardedRhs _ es ds) = (Let NoSpanInfo ds . f)
                                   <$> expandGuards e0 es

expandGuards :: Expression PredType -> [CondExpr PredType]
             -> DsM (Expression PredType)
expandGuards e0 es =
  return $ if boolGuards es then foldr mkIfThenElse e0 es else mkCond es
  where
  mkIfThenElse (CondExpr _ g e) = IfThenElse NoSpanInfo g e
  mkCond [CondExpr _ g e] = g &> e
  mkCond _                = error "Desugar.expandGuards.mkCond: non-unary list"

boolGuards :: [CondExpr PredType] -> Bool
boolGuards []                    = False
boolGuards (CondExpr _ g _ : es) = not (null es) || typeOf g == boolType

-- Add additional declarations to a right-hand side
addDecls :: [Decl PredType] -> Rhs PredType -> Rhs PredType
addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
addDecls ds (GuardedRhs spi es ds') = GuardedRhs spi es (ds ++ ds')

-- -----------------------------------------------------------------------------
-- Desugaring of non-linear patterns
-- -----------------------------------------------------------------------------

-- The desugaring traverses a pattern in depth-first order and collects
-- all variables. If it encounters a variable which has been previously
-- introduced, the second occurrence is changed to a fresh variable
-- and a new pair (newvar, oldvar) is saved to generate constraints later.
-- Non-linear patterns inside single functional patterns are not desugared,
-- as this special case is handled later.
dsNonLinearity :: [Pattern PredType]
               -> DsM ([Expression PredType], [Pattern PredType])
dsNonLinearity ts = do
  ((_, cs), ts') <- mapAccumM dsNonLinear (Set.empty, []) ts
  return (reverse cs, ts')

type NonLinearEnv = (Set.Set Ident, [Expression PredType])

dsNonLinear :: NonLinearEnv -> Pattern PredType
            -> DsM (NonLinearEnv, Pattern PredType)
dsNonLinear env l@(LiteralPattern        _ _ _) = return (env, l)
dsNonLinear env n@(NegativePattern       _ _ _) = return (env, n)
dsNonLinear env t@(VariablePattern       _ _ v)
  | isAnonId v         = return (env, t)
  | v `Set.member` vis = do
    v' <- freshVar "_#nonlinear" t
    return ((vis, mkStrictEquality v v' : eqs),
             uncurry (VariablePattern NoSpanInfo) v')
  | otherwise          = return ((Set.insert v vis, eqs), t)
  where (vis, eqs) = env
dsNonLinear env (ConstructorPattern _ pty c ts)
  = second (ConstructorPattern NoSpanInfo pty c) <$> mapAccumM dsNonLinear env ts
dsNonLinear env (InfixPattern   _ pty t1 op t2) = do
  (env1, t1') <- dsNonLinear env  t1
  (env2, t2') <- dsNonLinear env1 t2
  return (env2, InfixPattern NoSpanInfo pty t1' op t2')
dsNonLinear env (ParenPattern              _ t) =
  second (ParenPattern NoSpanInfo) <$> dsNonLinear env t
dsNonLinear env (RecordPattern      _ pty c fs) =
  second (RecordPattern NoSpanInfo pty c)
  <$> mapAccumM (dsField dsNonLinear) env fs
dsNonLinear env (TuplePattern             _ ts) =
  second (TuplePattern NoSpanInfo) <$> mapAccumM dsNonLinear env ts
dsNonLinear env (ListPattern          _ pty ts) =
  second (ListPattern NoSpanInfo pty) <$> mapAccumM dsNonLinear env ts
dsNonLinear env (AsPattern               _ v t) = do
  let pty = predType $ typeOf t
  (env1, pat) <- dsNonLinear env (VariablePattern NoSpanInfo pty v)
  let VariablePattern _ _ v' = pat
  (env2, t') <- dsNonLinear env1 t
  return (env2, AsPattern NoSpanInfo v' t')
dsNonLinear env (LazyPattern               _ t) =
  second (LazyPattern NoSpanInfo) <$> dsNonLinear env t
dsNonLinear env fp@(FunctionPattern    _ _ _ _) = dsNonLinearFuncPat env fp
dsNonLinear env fp@(InfixFuncPattern _ _ _ _ _) = dsNonLinearFuncPat env fp

dsNonLinearFuncPat :: NonLinearEnv -> Pattern PredType
                   -> DsM (NonLinearEnv, Pattern PredType)
dsNonLinearFuncPat (vis, eqs) fp = do
  let fpVars = map (\(v, _, pty) -> (pty, v)) $ patternVars fp
      vs     = filter ((`Set.member` vis) . snd) fpVars
  vs' <- mapM (freshVar "_#nonlinear" . uncurry (VariablePattern NoSpanInfo)) vs
  let vis' = foldr (Set.insert . snd) vis fpVars
      fp'  = substPat (zip (map snd vs) (map snd vs')) fp
  return ((vis', zipWith mkStrictEquality (map snd vs) vs' ++ eqs), fp')

mkStrictEquality :: Ident -> (PredType, Ident) -> Expression PredType
mkStrictEquality x (pty, y) = mkVar pty x =:= mkVar pty y

substPat :: [(Ident, Ident)] -> Pattern a -> Pattern a
substPat _ l@(LiteralPattern        _ _ _) = l
substPat _ n@(NegativePattern       _ _ _) = n
substPat s (VariablePattern         _ a v) =
  VariablePattern NoSpanInfo a $ fromMaybe v (lookup v s)

substPat s (ConstructorPattern   _ a c ps) =
  ConstructorPattern NoSpanInfo a c $ map (substPat s) ps
substPat s (InfixPattern     _ a p1 op p2) =
  InfixPattern NoSpanInfo a (substPat s p1) op (substPat s p2)
substPat s (ParenPattern              _ p) =
  ParenPattern NoSpanInfo (substPat s p)
substPat s (RecordPattern        _ a c fs) =
  RecordPattern NoSpanInfo a c (map substField fs)
  where substField (Field pos l pat) = Field pos l (substPat s pat)
substPat s (TuplePattern             _ ps) =
  TuplePattern NoSpanInfo $ map (substPat s) ps
substPat s (ListPattern            _ a ps) =
  ListPattern NoSpanInfo a $ map (substPat s) ps
substPat s (AsPattern               _ v p) =
  AsPattern NoSpanInfo (fromMaybe v (lookup v s)) (substPat s p)
substPat s (LazyPattern               _ p) =
  LazyPattern NoSpanInfo (substPat s p)
substPat s (FunctionPattern      _ a f ps) =
  FunctionPattern NoSpanInfo a f $ map (substPat s) ps
substPat s (InfixFuncPattern _ a p1 op p2) =
  InfixFuncPattern NoSpanInfo a (substPat s p1) op (substPat s p2)

-- -----------------------------------------------------------------------------
-- Desugaring of functional patterns
-- -----------------------------------------------------------------------------

-- Desugaring of functional patterns works in the following way:
--  1. The patterns are recursively traversed from left to right
--     to extract every functional pattern (note that functional patterns
--     can not be nested).
--     Each pattern is replaced by a fresh variable and a pair
--     (variable, functional pattern) is generated.
--  2. The variable-pattern pairs of the form @(v, p)@ are collected and
--     transformed into additional constraints of the form @p =:<= v@,
--     where the pattern @p@ is converted to the corresponding expression.
--     In addition, any variable occurring in @p@ is declared as a fresh
--     free variable.
--     Multiple constraints will later be combined using the @&>@-operator
--     such that the patterns are evaluated from left to right.

dsFunctionalPatterns
  :: SpanInfo -> [Pattern PredType]
  -> DsM ([Decl PredType], Expression PredType -> Expression PredType, [Pattern PredType])
dsFunctionalPatterns p ts = do
  -- extract functional patterns
  (bs, ts') <- mapAccumM elimFP [] ts
  -- generate declarations of free variables and constraints
  mid   <- getModuleIdent
  allDs <- S.gets allDecls
  let revbs = reverse bs
  let free = nub $ filter (not . isAnonId . fst3) $
                   concatMap (patternVars . fst) revbs
                     \\ concatMap patternVars ts'
  if all (isLinearFuncPat mid allDs . fst) bs
    -- return (declarations, constraints, desugared patterns)
    then let fCond = genLinFPExpr        revbs in return ([], fCond       , ts')
    else let (ds, cs) = genFPExpr p free revbs in return (ds, constrain cs, ts')

type LazyBinding = (Pattern PredType, (PredType, Ident))

elimFP :: [LazyBinding] -> Pattern PredType
       -> DsM ([LazyBinding], Pattern PredType)
elimFP bs p@(LiteralPattern        _ _ _) = return (bs, p)
elimFP bs p@(NegativePattern       _ _ _) = return (bs, p)
elimFP bs p@(VariablePattern       _ _ _) = return (bs, p)
elimFP bs (ConstructorPattern _ pty c ts) =
  second (ConstructorPattern NoSpanInfo  pty c) <$> mapAccumM elimFP bs ts
elimFP bs (InfixPattern   _ pty t1 op t2) = do
  (bs1, t1') <- elimFP bs  t1
  (bs2, t2') <- elimFP bs1 t2
  return (bs2, InfixPattern NoSpanInfo pty t1' op t2')
elimFP bs (ParenPattern              _ t) =
  second (ParenPattern NoSpanInfo) <$> elimFP bs t
elimFP bs (RecordPattern      _ pty c fs) =
  second (RecordPattern NoSpanInfo pty c) <$> mapAccumM (dsField elimFP) bs fs
elimFP bs (TuplePattern             _ ts) =
  second (TuplePattern NoSpanInfo) <$> mapAccumM elimFP bs ts
elimFP bs (ListPattern          _ pty ts) =
  second (ListPattern NoSpanInfo pty) <$> mapAccumM elimFP bs ts
elimFP bs (AsPattern               _ v t) =
  second (AsPattern NoSpanInfo v) <$> elimFP bs t
elimFP bs (LazyPattern               _ t) =
  second (LazyPattern NoSpanInfo) <$> elimFP bs t
elimFP bs p@(FunctionPattern    _  _ _ _) = do
 (pty, v) <- freshVar "_#funpatt" p
 return ((p, (pty, v)) : bs, VariablePattern NoSpanInfo pty v)
elimFP bs p@(InfixFuncPattern  _ _ _ _ _) = do
 (pty, v) <- freshVar "_#funpatt" p
 return ((p, (pty, v)) : bs, VariablePattern NoSpanInfo pty v)

genFPExpr :: SpanInfo -> [(Ident, Int, PredType)] -> [LazyBinding]
          -> ([Decl PredType], [Expression PredType])
genFPExpr p free bs
  | null bs   = ([]               , [])
  | null free = ([]               , cs)
  | otherwise = ([FreeDecl p (map (\(v, _, pty) -> Var pty v) free)], cs)
  where
  mkLB (t, (pty, v)) = let (t', es) = fp2Expr t
                       in  (t' =:<= mkVar pty v) : es
  cs   = concatMap mkLB bs

fp2Expr :: Pattern PredType -> (Expression PredType, [Expression PredType])
fp2Expr (LiteralPattern          _ pty l) = (Literal NoSpanInfo  pty l, [])
fp2Expr (NegativePattern         _ pty l) =
  (Literal NoSpanInfo pty (negateLiteral l), [])
fp2Expr (VariablePattern         _ pty v) = (mkVar pty v, [])
fp2Expr (ConstructorPattern  _  pty c ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
      pty' = predType $ foldr (TypeArrow . typeOf) (unpredType pty) ts
  in  (apply (Constructor NoSpanInfo pty' c) ts', concat ess)
fp2Expr (InfixPattern   _ pty t1 op t2) =
  let (t1', es1) = fp2Expr t1
      (t2', es2) = fp2Expr t2
      pty' = predType $ foldr TypeArrow (unpredType pty) [typeOf t1, typeOf t2]
  in  (InfixApply NoSpanInfo t1' (InfixConstr pty' op) t2', es1 ++ es2)
fp2Expr (ParenPattern                _ t) = first (Paren NoSpanInfo) (fp2Expr t)
fp2Expr (TuplePattern               _ ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (Tuple NoSpanInfo ts', concat ess)
fp2Expr (ListPattern            _ pty ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (List NoSpanInfo pty ts', concat ess)
fp2Expr (FunctionPattern      _ pty f ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
      pty' = predType $ foldr (TypeArrow . typeOf) (unpredType pty) ts
  in  (apply (Variable NoSpanInfo pty' f) ts', concat ess)
fp2Expr (InfixFuncPattern _ pty t1 op t2) =
  let (t1', es1) = fp2Expr t1
      (t2', es2) = fp2Expr t2
      pty' = predType $ foldr (TypeArrow . typeOf) (unpredType pty) [t1, t2]
  in  (InfixApply NoSpanInfo t1' (InfixOp pty' op) t2', es1 ++ es2)
fp2Expr (AsPattern                 _ v t) =
  let (t', es) = fp2Expr t
      pty = predType $ typeOf t
  in  (mkVar pty v, (t' =:<= mkVar pty v) : es)
fp2Expr (RecordPattern        _ pty c fs) =
  let (fs', ess) = unzip [ (Field p f e, es) | Field p f t <- fs
                                             , let (e, es) = fp2Expr t]
  in  (Record NoSpanInfo pty c fs', concat ess)
fp2Expr t                               = internalError $
  "Desugar.fp2Expr: Unexpected constructor term: " ++ show t

-- TODO: pattern might be nonlinear

genLinFPExpr :: [LazyBinding] -> Expression PredType -> Expression PredType
genLinFPExpr []                     e = e
genLinFPExpr ((t, (pty, v)) : bs) e =
  let (f, ps) = fp2Pat t
      tys = map typeOf ps

      varty  = unpredType pty
      resty  = case tys of
        []  -> error "Desugar.genLinFPExpr: Empty pattern list"
        [x] -> x
        _   -> tupleType tys
      funty  = foldr TypeArrow varty tys
      invty  = TypeArrow funty (TypeArrow varty resty)

      invexpr  = (var (predType invty) (qInvfId (length ps))
              -=> var (predType funty) f)
              -=> var (predType varty) (qualify v)
      resexpr  = genLinFPExpr bs e
      failexpr = prelFailed (typeOf resexpr)

      succpat = case ps of
        []   -> error "Desugar.genLinFPExpr: Empty pattern list"
        [x]  -> x
        _    -> TuplePattern    NoSpanInfo ps
      failpat = VariablePattern NoSpanInfo (predType resty) anonId

  in Case NoSpanInfo Rigid invexpr
       [ Alt NoSpanInfo succpat (simpleRhs NoSpanInfo resexpr)
       , Alt NoSpanInfo failpat (simpleRhs NoSpanInfo failexpr)]
  where
    (-=>) = Apply NoSpanInfo
    var = Variable NoSpanInfo

fp2Pat :: Pattern PredType -> (QualIdent, [Pattern PredType])
fp2Pat (FunctionPattern  _ _    qid ps) = (qid, ps)
fp2Pat (InfixFuncPattern _ _ p1 qid p2) = (qid, [p1, p2])
fp2Pat _                                = error "Desugar.fp2pat: No functional pattern"

isLinearFuncPat :: ModuleIdent -> [Decl PredType] -> Pattern PredType -> Bool
isLinearFuncPat mid ds (FunctionPattern  _ _   qid _) = isLinearIdt mid ds qid
isLinearFuncPat mid ds (InfixFuncPattern _ _ _ qid _) = isLinearIdt mid ds qid
isLinearFuncPat _   _  _                              = False

-- -----------------------------------------------------------------------------
-- Desugaring of ordinary patterns
-- -----------------------------------------------------------------------------

-- The transformation of patterns is straight forward except for lazy
-- patterns. A lazy pattern '~t' is replaced by a fresh
-- variable 'v' and a new local declaration 't = v' in the
-- scope of the pattern. In addition, as-patterns 'v@t' where
-- 't' is a variable or an as-pattern are replaced by 't' in combination
-- with a local declaration for 'v'.

-- Record patterns are transformed into normal constructor patterns by
-- rearranging fields in the order of the record's declaration, adding
-- fresh variables in place of omitted fields, and discarding the field
-- labels.

-- Note: By rearranging fields here we loose the ability to comply
-- strictly with the Haskell 98 pattern matching semantics, which matches
-- fields of a record pattern in the order of their occurrence in the
-- pattern. However, keep in mind that Haskell matches alternatives from
-- top to bottom and arguments within an equation or alternative from
-- left to right, which is not the case in Curry except for rigid case
-- expressions.

dsLiteralPat :: PredType -> Literal
             -> Either (Pattern PredType) (Pattern PredType)
dsLiteralPat pty c@(Char _) = Right (LiteralPattern NoSpanInfo pty c)
dsLiteralPat pty (Int i) =
  Right (LiteralPattern NoSpanInfo pty (fixLiteral (unpredType pty)))
  where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
        fixLiteral ty
          | ty == floatType = Float $ fromInteger i
          | otherwise = Int i
dsLiteralPat pty f@(Float _) = Right (LiteralPattern NoSpanInfo pty f)
dsLiteralPat pty (String cs) =
  Left $ ListPattern NoSpanInfo pty $
  map (LiteralPattern NoSpanInfo pty' . Char) cs
  where pty' = predType $ elemType $ unpredType pty

dsPat :: SpanInfo -> [Decl PredType] -> Pattern PredType
      -> DsM ([Decl PredType], Pattern PredType)
dsPat _ ds v@(VariablePattern       _ _ _) = return (ds, v)
dsPat p ds (LiteralPattern      _ pty l) =
  either (dsPat p ds) (return . (,) ds) (dsLiteralPat pty l)
dsPat p ds (NegativePattern       _ pty l) =
  dsPat p ds (LiteralPattern NoSpanInfo pty (negateLiteral l))
dsPat p ds (ConstructorPattern _ pty c ts) =
  second (ConstructorPattern NoSpanInfo pty c) <$> mapAccumM (dsPat p) ds ts
dsPat p ds (InfixPattern   _ pty t1 op t2) =
  dsPat p ds (ConstructorPattern NoSpanInfo pty op [t1, t2])
dsPat p ds (ParenPattern              _ t) = dsPat p ds t
dsPat p ds (RecordPattern      _ pty c fs) = do
  vEnv <- getValueEnv
  --TODO: Rework
  let (ls, tys) = argumentTypes (unpredType pty) c vEnv
      tsMap = map field2Tuple fs
  anonTs <- mapM ((uncurry (VariablePattern NoSpanInfo) <$>) .
                  freshVar "_#recpat") tys
  let maybeTs = map (flip lookup tsMap) ls
      ts = zipWith fromMaybe anonTs maybeTs
  dsPat p ds (ConstructorPattern NoSpanInfo pty c ts)
dsPat p ds (TuplePattern              _ ts) =
  dsPat p ds (ConstructorPattern NoSpanInfo pty (qTupleId $ length ts) ts)
  where pty = predType (tupleType (map typeOf ts))
dsPat p ds (ListPattern           _ pty ts) =
  second (dsList cons nil) <$> mapAccumM (dsPat p) ds ts
  where nil = ConstructorPattern NoSpanInfo pty qNilId []
        cons t ts' = ConstructorPattern NoSpanInfo pty qConsId [t, ts']
dsPat p ds (AsPattern            _ v t) = dsAs p v <$> dsPat p ds t
dsPat p ds (LazyPattern            _ t) = dsLazy p ds t
dsPat p ds (FunctionPattern   _   pty f ts) =
  second (FunctionPattern NoSpanInfo pty f) <$> mapAccumM (dsPat p) ds ts
dsPat p ds (InfixFuncPattern _ pty t1 f t2) =
  dsPat p ds (FunctionPattern NoSpanInfo pty f [t1, t2])

dsAs :: SpanInfo -> Ident -> ([Decl PredType], Pattern PredType)
     -> ([Decl PredType], Pattern PredType)
dsAs p v (ds, t) = case t of
  VariablePattern _ pty v' -> (varDecl p pty  v (mkVar pty  v') : ds,t)
  AsPattern       _  v' t' -> (varDecl p pty' v (mkVar pty' v') : ds,t)
    where pty' = predType $ typeOf t'
  _                      -> (ds, AsPattern NoSpanInfo v t)

dsLazy :: SpanInfo -> [Decl PredType] -> Pattern PredType
       -> DsM ([Decl PredType], Pattern PredType)
dsLazy p ds t = case t of
  VariablePattern _ _ _ -> return (ds, t)
  ParenPattern     _ t' -> dsLazy p ds t'
  AsPattern      _ v t' -> dsAs p v <$> dsLazy p ds t'
  LazyPattern      _ t' -> dsLazy p ds t'
  _                 -> do
    (pty, v') <- freshVar "_#lazy" t
    return (patDecl NoSpanInfo t (mkVar pty v') : ds,
            VariablePattern NoSpanInfo pty v')

{-
-- -----------------------------------------------------------------------------
-- Desugaring of expressions
-- -----------------------------------------------------------------------------

-- Record construction expressions are transformed into normal
-- constructor applications by rearranging fields in the order of the
-- record's declaration, passing `Prelude.unknown` in place of
-- omitted fields, and discarding the field labels. The transformation of
-- record update expressions is a bit more involved as we must match the
-- updated expression with all valid constructors of the expression's
-- type. As stipulated by the Haskell 98 Report, a record update
-- expression @e { l_1 = e_1, ..., l_k = e_k }@ succeeds only if @e@ reduces to
-- a value @C e'_1 ... e'_n@ such that @C@'s declaration contains all
-- field labels @l_1,...,l_k@. In contrast to Haskell, we do not report
-- an error if this is not the case, but call failed instead.
-}
dsExpr :: SpanInfo -> Expression PredType -> DsM (Expression PredType)
dsExpr p (Literal     _ pty l) =
  either (dsExpr p) return (dsLiteral pty l)
dsExpr _ var@(Variable _ pty v)
  | isAnonId (unqualify v)   = return $ prelUnknown $ unpredType pty
  | otherwise                = return var
dsExpr _ c@(Constructor _ _ _) = return c
dsExpr p (Paren           _ e) = dsExpr p e
dsExpr p (Typed       _ e qty) = Typed NoSpanInfo
  <$> dsExpr p e <*> dsQualTypeExpr qty
dsExpr p (Record   _ pty c fs) = do
  vEnv <- getValueEnv
  --TODO: Rework
  let (ls, tys) = argumentTypes (unpredType pty) c vEnv
      esMap = map field2Tuple fs
      unknownEs = map prelUnknown tys
      maybeEs = map (flip lookup esMap) ls
      es = zipWith fromMaybe unknownEs maybeEs
  dsExpr p (applyConstr pty c tys es)
dsExpr p (RecordUpdate _ e fs) = do
  alts  <- constructors tc >>= concatMapM updateAlt
  dsExpr p $ Case NoSpanInfo Flex e (map (uncurry (caseAlt p)) alts)
  where ty = typeOf e
        pty = predType ty
        tc = rootOfType (arrowBase ty)
        updateAlt (RecordConstr c ls _)
          | all (`elem` qls2) (map fieldLabel fs)= do
            let qc = qualifyLike tc c
            vEnv <- getValueEnv
            let (qls, tys) = argumentTypes ty qc vEnv
            vs <- mapM (freshVar "_#rec") tys
            let pat = constrPattern pty qc vs
                esMap = map field2Tuple fs
                originalEs = map (uncurry mkVar) vs
                maybeEs = map (flip lookup esMap) qls
                es = zipWith fromMaybe originalEs maybeEs
            return [(pat, applyConstr pty qc tys es)]
          where qls2 = map (qualifyLike tc) ls
        updateAlt _ = return []
dsExpr p (Tuple      _ es) =
  apply (Constructor NoSpanInfo pty $ qTupleId $ length es)
  <$> mapM (dsExpr p) es
  where pty = predType (foldr TypeArrow (tupleType tys) tys)
        tys = map typeOf es
dsExpr p (List   _ pty es) = dsList cons nil <$> mapM (dsExpr p) es
  where nil = Constructor NoSpanInfo pty qNilId
        cons = (Apply NoSpanInfo) . (Apply NoSpanInfo)
          (Constructor NoSpanInfo
            (predType $ consType $ elemType $ unpredType pty) qConsId)
dsExpr p (ListCompr          _ e qs) = dsListComp p e qs
dsExpr p (EnumFrom              _ e) =
  Apply NoSpanInfo (prelEnumFrom (typeOf e)) <$> dsExpr p e
dsExpr p (EnumFromThen      _ e1 e2) =
  apply (prelEnumFromThen (typeOf e1)) <$> mapM (dsExpr p) [e1, e2]
dsExpr p (EnumFromTo        _ e1 e2) = apply (prelEnumFromTo (typeOf e1))
                                    <$> mapM (dsExpr p) [e1, e2]
dsExpr p (EnumFromThenTo _ e1 e2 e3) = apply (prelEnumFromThenTo (typeOf e1))
                                    <$> mapM (dsExpr p) [e1, e2, e3]
dsExpr p (UnaryMinus            _ e) = do
  e' <- dsExpr p e
  negativeLitsEnabled <- checkNegativeLitsExtension
  return $ case e' of
    Literal _ pty l | negativeLitsEnabled ->
      Literal NoSpanInfo pty $ negateLiteral l
    _                                     ->
      Apply NoSpanInfo (prelNegate $ typeOf e') e'
dsExpr p (Apply _ e1 e2) = Apply NoSpanInfo <$> dsExpr p e1 <*> dsExpr p e2
dsExpr p (InfixApply _ e1 op e2) = do
  op' <- dsExpr p (infixOp op)
  e1' <- dsExpr p e1
  e2' <- dsExpr p e2
  return $ apply op' [e1', e2']
dsExpr p (LeftSection  _ e op) =
  Apply NoSpanInfo <$> dsExpr p (infixOp op) <*> dsExpr p e
dsExpr p (RightSection _ op e) = do
  op' <- dsExpr p (infixOp op)
  e'  <- dsExpr p e
  return $ apply (prelFlip ty1 ty2 ty3) [op', e']
  where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf (infixOp op)
dsExpr p expr@(Lambda _ ts e) = do
  (pty, f) <- freshVar "_#lambda" expr
  dsExpr p $ Let NoSpanInfo [funDecl p pty f ts e] $ mkVar pty f
dsExpr p (Let _ ds e) = do
  ds' <- dsDeclGroup ds
  e'  <- dsExpr p e
  return (if null ds' then e' else Let NoSpanInfo ds' e')
dsExpr p (Do              _ sts e) = dsDo sts e >>= dsExpr p
dsExpr p (IfThenElse _ e1 e2 e3) = do
  e1' <- dsExpr p e1
  e2' <- dsExpr p e2
  e3' <- dsExpr p e3
  return $ Case NoSpanInfo Rigid e1'
             [caseAlt p truePat e2', caseAlt p falsePat e3']
dsExpr p (Case _ ct e alts) = dsCase p ct e alts

-- We ignore the context in the type signature of a typed expression, since
-- there should be no possibility to provide an non-empty context without
-- scoped type-variables.
-- TODO: Verify

dsQualTypeExpr :: QualTypeExpr -> DsM QualTypeExpr
dsQualTypeExpr (QualTypeExpr _ cx ty) =
  QualTypeExpr NoSpanInfo cx <$> dsTypeExpr ty

dsTypeExpr :: TypeExpr -> DsM TypeExpr
dsTypeExpr ty = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  return $ fromType (typeVariables ty) (expandType m tcEnv (toType [] ty))

-- -----------------------------------------------------------------------------
-- Desugaring of case expressions
-- -----------------------------------------------------------------------------

-- If an alternative in a case expression has boolean guards and all of
-- these guards return 'False', the enclosing case expression does
-- not fail but continues to match the remaining alternatives against the
-- selector expression. In order to implement this semantics, which is
-- compatible with Haskell, we expand an alternative with boolean guards
-- such that it evaluates a case expression with the remaining cases that
-- are compatible with the matched pattern when the guards fail.

dsCase :: SpanInfo -> CaseType -> Expression PredType -> [Alt PredType]
       -> DsM (Expression PredType)
dsCase p ct e alts
  | null alts = internalError "Desugar.dsCase: empty list of alternatives"
  | otherwise = do
    m  <- getModuleIdent
    e' <- dsExpr p e
    v  <- freshVar "_#case" e
    alts'  <- mapM dsAltLhs alts
    alts'' <- mapM (expandAlt v ct) (init (tails alts')) >>= mapM dsAltRhs
    return (mkCase m v e' alts'')
  where
  mkCase m (pty, v) e' bs
    | v `elem` qfv m bs = Let NoSpanInfo [varDecl p pty v e']
                          (Case NoSpanInfo ct (mkVar pty v) bs)
    | otherwise         = Case NoSpanInfo ct e' bs

dsAltLhs :: Alt PredType -> DsM (Alt PredType)
dsAltLhs (Alt p t rhs) = do
  (ds', t') <- dsPat p [] t
  return $ Alt p t' (addDecls ds' rhs)

dsAltRhs :: Alt PredType -> DsM (Alt PredType)
dsAltRhs (Alt p t rhs) = Alt p t <$> dsRhs id rhs

expandAlt :: (PredType, Ident) -> CaseType -> [Alt PredType]
          -> DsM (Alt PredType)
expandAlt _ _  []                   = error "Desugar.expandAlt: empty list"
expandAlt v ct (Alt p t rhs : alts) = caseAlt p t <$> expandRhs e0 id rhs
  where
  e0 | ct == Flex || null compAlts = prelFailed (typeOf rhs)
     | otherwise = Case NoSpanInfo ct (uncurry mkVar v) compAlts
  compAlts = filter (isCompatible t . altPattern) alts
  altPattern (Alt _ t1 _) = t1

isCompatible :: Pattern a -> Pattern a -> Bool
isCompatible (VariablePattern _ _ _) _ = True
isCompatible _ (VariablePattern _ _ _) = True
isCompatible (AsPattern _ _ t1) t2 = isCompatible t1 t2
isCompatible t1 (AsPattern _ _ t2) = isCompatible t1 t2
isCompatible (ConstructorPattern _ _ c1 ts1) (ConstructorPattern _ _ c2 ts2)
  = and ((c1 == c2) : zipWith isCompatible ts1 ts2)
isCompatible (LiteralPattern _ _ l1) (LiteralPattern _ _ l2) = l1 == l2
isCompatible _ _ = False

-- -----------------------------------------------------------------------------
-- Desugaring of do-Notation
-- -----------------------------------------------------------------------------

-- The do-notation is desugared in the following way:
--
-- `dsDo([]         , e)` -> `e`
-- `dsDo(e'     ; ss, e)` -> `e' >>        dsDo(ss, e)`
-- `dsDo(p <- e'; ss, e)` -> `e' >>= \v -> case v of
--                                           p -> dsDo(ss, e)
--                                           _ -> fail "..."`
-- `dsDo(let ds ; ss, e)` -> `let ds in    dsDo(ss, e)`
dsDo :: [Statement PredType] -> Expression PredType -> DsM (Expression PredType)
dsDo sts e = foldrM dsStmt e sts

dsStmt :: Statement PredType -> Expression PredType -> DsM (Expression PredType)
dsStmt (StmtExpr   _ e1) e' =
  return $ apply (prelBind_ (typeOf e1) (typeOf e')) [e1, e']
dsStmt (StmtBind _ t e1) e' = do
  v <- freshVar "_#var" t
  let func = Lambda NoSpanInfo [uncurry (VariablePattern NoSpanInfo) v] $
               Case NoSpanInfo Rigid (uncurry mkVar v)
                 [ caseAlt NoSpanInfo t e'
                 , caseAlt NoSpanInfo (uncurry (VariablePattern NoSpanInfo) v)
                     (failedPatternMatch $ typeOf e')
                 ]
  return $ apply (prelBind (typeOf e1) (typeOf t) (typeOf e')) [e1, func]
  where failedPatternMatch ty =
          apply (prelFail ty)
            [Literal NoSpanInfo predStringType $ String "Pattern match failed!"]
dsStmt (StmtDecl   _ ds) e' = return $ Let NoSpanInfo ds e'

-- -----------------------------------------------------------------------------
-- Desugaring of List Comprehensions
-- -----------------------------------------------------------------------------

-- In general, a list comprehension of the form
-- '[e | t <- l, qs]'
-- is transformed into an expression 'foldr f [] l' where 'f'
-- is a new function defined as
--
--     f x xs =
--       case x of
--           t -> [e | qs] ++ xs
--           _ -> xs
--
-- Note that this translation evaluates the elements of 'l' rigidly,
-- whereas the translation given in the Curry report is flexible.
-- However, it does not seem very useful to have the comprehension
-- generate instances of 't' which do not contribute to the list.
-- TODO: Unfortunately, this is incorrect.

-- Actually, we generate slightly better code in a few special cases.
-- When 't' is a plain variable, the 'case' expression degenerates
-- into a let-binding and the auxiliary function thus becomes an alias
-- for '(++)'. Instead of 'foldr (++)' we use the
-- equivalent prelude function 'concatMap'. In addition, if the
-- remaining list comprehension in the body of the auxiliary function has
-- no qualifiers -- i.e., if it is equivalent to '[e]' -- we
-- avoid the construction of the singleton list by calling '(:)'
-- instead of '(++)' and 'map' in place of 'concatMap', respectively.

dsListComp :: SpanInfo -> Expression PredType -> [Statement PredType]
           -> DsM (Expression PredType)
dsListComp p e []     =
  dsExpr p (List NoSpanInfo (predType $ listType $ typeOf e) [e])
dsListComp p e (q:qs) = dsQual p q (ListCompr NoSpanInfo e qs)

dsQual :: SpanInfo -> Statement PredType -> Expression PredType
       -> DsM (Expression PredType)
dsQual p (StmtExpr   _ b) e =
  dsExpr p (IfThenElse NoSpanInfo b e (List NoSpanInfo (predType $ typeOf e) []))
dsQual p (StmtDecl  _ ds) e = dsExpr p (Let NoSpanInfo ds e)
dsQual p (StmtBind _ t l) e
  | isVariablePattern t = dsExpr p (qualExpr t e l)
  | otherwise = do
    v <- freshVar "_#var" t
    l' <- freshVar "_#var" e
    dsExpr p (apply (prelFoldr (typeOf t) (typeOf e))
      [foldFunct v l' e, List NoSpanInfo (predType $ typeOf e) [], l])
  where
  qualExpr v (ListCompr NoSpanInfo e1 []) l1
    = apply (prelMap (typeOf v) (typeOf e1)) [Lambda NoSpanInfo [v] e1, l1]
  qualExpr v e1                  l1
    = apply (prelConcatMap (typeOf v) (elemType $ typeOf e1))
      [Lambda NoSpanInfo [v] e1, l1]
  foldFunct v l1 e1
    = Lambda NoSpanInfo (map (uncurry (VariablePattern NoSpanInfo)) [v, l1])
       (Case NoSpanInfo Rigid (uncurry mkVar v)
          [ caseAlt p t (append e1 (uncurry mkVar l1))
          , caseAlt p (uncurry (VariablePattern NoSpanInfo) v)
                                    (uncurry mkVar l1)])

  append (ListCompr _ e1 []) l1 = apply (prelCons (typeOf e1)) [e1, l1]
  append e1                  l1 =
    apply (prelAppend (elemType $ typeOf e1)) [e1, l1]
  prelCons ty                   =
      Constructor NoSpanInfo (predType $ consType ty) $ qConsId

-- -----------------------------------------------------------------------------
-- Desugaring of Lists, labels, fields, and literals
-- -----------------------------------------------------------------------------

dsList :: (b -> b -> b) -> b -> [b] -> b
dsList = foldr

--dsLabel :: a -> [(QualIdent, a)] -> QualIdent -> a
--dsLabel def fs l = fromMaybe def (lookup l fs)

dsField :: (a -> b -> DsM (a, b)) -> a -> Field b -> DsM (a, Field b)
dsField ds z (Field p l x) = second (Field p l) <$> ds z x

dsLiteral :: PredType -> Literal
          -> Either (Expression PredType) (Expression PredType)
dsLiteral pty (Char c) = Right $ Literal NoSpanInfo pty $ Char c
dsLiteral pty (Int i) = Right $ fixLiteral (unpredType pty)
  where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
        fixLiteral ty
          | ty == intType = Literal NoSpanInfo pty $ Int i
          | ty == floatType = Literal NoSpanInfo pty $ Float $ fromInteger i
          | otherwise = Apply NoSpanInfo (prelFromInt $ unpredType pty) $
                          Literal NoSpanInfo predIntType $ Int i
dsLiteral pty f@(Float _) = Right $ fixLiteral (unpredType pty)
  where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
        fixLiteral ty
          | ty == floatType = Literal NoSpanInfo pty f
          | otherwise = Apply NoSpanInfo (prelFromFloat $ unpredType pty) $
                          Literal NoSpanInfo predFloatType f
dsLiteral pty (String cs) =
  Left $ List NoSpanInfo pty $ map (Literal NoSpanInfo pty' . Char) cs
  where pty' = predType $ elemType $ unpredType pty

negateLiteral :: Literal -> Literal
negateLiteral (Int i) = Int (-i)
negateLiteral (Float f) = Float (-f)
negateLiteral _ = internalError "Desugar.negateLiteral"

-- ---------------------------------------------------------------------------
-- Prelude entities
-- ---------------------------------------------------------------------------

preludeFun :: [Type] -> Type -> String -> Expression PredType
preludeFun tys ty = Variable NoSpanInfo (predType $ foldr TypeArrow ty tys)
                  . preludeIdent

preludeIdent :: String -> QualIdent
preludeIdent = qualifyWith preludeMIdent . mkIdent

prelBind :: Type -> Type -> Type -> Expression PredType
prelBind ma a mb = preludeFun [ma, TypeArrow a mb] mb ">>="

prelBind_ :: Type -> Type -> Expression PredType
prelBind_ ma mb = preludeFun [ma, mb] mb ">>"

prelFlip :: Type -> Type -> Type -> Expression PredType
prelFlip a b c = preludeFun [TypeArrow a (TypeArrow b c), b, a] c "flip"

prelFromInt :: Type -> Expression PredType
prelFromInt a = preludeFun [intType] a "fromInt"

prelFromFloat :: Type -> Expression PredType
prelFromFloat a = preludeFun [floatType] a "fromFloat"

prelEnumFrom :: Type -> Expression PredType
prelEnumFrom a = preludeFun [a] (listType a) "enumFrom"

prelEnumFromTo :: Type -> Expression PredType
prelEnumFromTo a = preludeFun [a, a] (listType a) "enumFromTo"

prelEnumFromThen :: Type -> Expression PredType
prelEnumFromThen a = preludeFun [a, a] (listType a) "enumFromThen"

prelEnumFromThenTo :: Type -> Expression PredType
prelEnumFromThenTo a = preludeFun [a, a, a] (listType a) "enumFromThenTo"

prelNegate :: Type -> Expression PredType
prelNegate a = preludeFun [a] a "negate"

prelFail :: Type -> Expression PredType
prelFail ma = preludeFun [stringType] ma "fail"

prelFailed :: Type -> Expression PredType
prelFailed a = preludeFun [] a "failed"

prelUnknown :: Type -> Expression PredType
prelUnknown a = preludeFun [] a "unknown"

prelMap :: Type -> Type -> Expression PredType
prelMap a b = preludeFun [TypeArrow a b, listType a] (listType b) "map"

prelFoldr :: Type -> Type -> Expression PredType
prelFoldr a b =
  preludeFun [TypeArrow a (TypeArrow b b), b, listType a] b "foldr"

prelAppend :: Type -> Expression PredType
prelAppend a = preludeFun [listType a, listType a] (listType a) "++"

prelConcatMap :: Type -> Type -> Expression PredType
prelConcatMap a b =
  preludeFun [TypeArrow a (listType b), listType a] (listType b) "concatMap"

(=:<=) :: Expression PredType -> Expression PredType -> Expression PredType
e1 =:<= e2 = apply (preludeFun [typeOf e1, typeOf e2] boolType "=:<=") [e1, e2]

(=:=) :: Expression PredType -> Expression PredType -> Expression PredType
e1 =:= e2 = apply (preludeFun [typeOf e1, typeOf e2] boolType "=:=") [e1, e2]

(&>) :: Expression PredType -> Expression PredType -> Expression PredType
e1 &> e2 = apply (preludeFun [boolType, typeOf e2] (typeOf e2) "cond") [e1, e2]

(&) :: Expression PredType -> Expression PredType -> Expression PredType
e1 & e2 = apply (preludeFun [boolType, boolType] boolType "&") [e1, e2]

truePat :: Pattern PredType
truePat = ConstructorPattern NoSpanInfo predBoolType qTrueId []

falsePat :: Pattern PredType
falsePat = ConstructorPattern NoSpanInfo predBoolType qFalseId []

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

conType :: QualIdent -> ValueEnv -> ([Ident], TypeScheme)
conType c vEnv = case qualLookupValue c vEnv of
  [DataConstructor _ _ ls ty] -> (ls , ty)
  [NewtypeConstructor _ l ty] -> ([l], ty)
  _                           -> internalError $ "Desguar.conType: " ++ show c

varType :: QualIdent -> ValueEnv -> TypeScheme
varType v vEnv = case qualLookupValue v vEnv of
  Value _ _ _ tySc : _ -> tySc
  Label _ _   tySc : _ -> tySc
  _                    -> internalError $ "Desugar.varType: " ++ show v

elemType :: Type -> Type
elemType (TypeApply (TypeConstructor tc) ty) | tc == qListId = ty
elemType ty = internalError $ "Base.Types.elemType " ++ show ty

applyConstr :: PredType -> QualIdent -> [Type] -> [Expression PredType]
            -> Expression PredType
applyConstr pty c tys =
  apply (Constructor NoSpanInfo
    (predType (foldr TypeArrow (unpredType pty) tys)) c)

-- The function 'instType' instantiates the universally quantified
-- type variables of a type scheme with fresh type variables. Since this
-- function is used only to instantiate the closed types of record
-- constructors (recall that no existentially quantified type
-- variables are allowed for records), the compiler can reuse the same
-- monomorphic type variables for every instantiated type.

instType :: TypeScheme -> Type
instType (ForAll _ pty) = inst $ unpredType pty
  where inst (TypeConstructor     tc) = TypeConstructor tc
        inst (TypeApply      ty1 ty2) = TypeApply (inst ty1) (inst ty2)
        inst (TypeVariable        tv) = TypeVariable (-1 - tv)
        inst (TypeArrow      ty1 ty2) = TypeArrow (inst ty1) (inst ty2)
        inst ty                       = ty

-- Retrieve all constructors of a type
constructors :: QualIdent -> DsM [DataConstr]
constructors tc = getTyConsEnv >>= \tcEnv -> return $
  case qualLookupTypeInfo tc tcEnv of
    [DataType     _ _ cs] -> cs
    [RenamingType _ _ nc] -> [nc]
    _                     ->
      internalError $ "Transformations.Desugar.constructors: " ++ show tc

-- The function 'argumentTypes' returns the labels and the argument types
-- of a data constructor instantiated at a particular type.

argumentTypes :: Type -> QualIdent -> ValueEnv -> ([QualIdent], [Type])
argumentTypes ty c vEnv =
  (map (qualifyLike c) ls, map (subst (matchType ty0 ty idSubst)) tys)
  where (ls, ForAll _ (PredType _ ty')) = conType c vEnv
        (tys, ty0) = arrowUnapply ty'
