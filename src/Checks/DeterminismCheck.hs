{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
module Checks.DeterminismCheck (determinismCheck, DetEnv) where

import Base.Types
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding ((<>))
import Data.Map (Map)
import qualified Data.Map as Map
import Curry.Syntax
import Curry.Base.Ident
import Base.Typing
import Control.Monad.State
import Env.Instance
import Env.Value
import Env.TypeConstructor
import Env.Class
import Base.Messages (Message, internalError)
import Base.SCC (scc)
import Base.Utils
import Curry.Base.Pretty
import qualified Data.IntSet as IntSet
import Curry.Base.SpanInfo
import Data.Maybe
import Data.List

type DetEnv = Map IdentInfo DetType

data IdentInfo = QI QualIdent
               | II QualIdent QualIdent QualIdent -- class, tycon, method
               | CI QualIdent QualIdent -- class, default method
  deriving (Eq, Ord, Show)

type VarIndex = Int

data DetType = VarTy VarIndex
             | Det
             | DetArrow DetType DetType
             | Nondet
  deriving (Eq, Ord, Show)

data DetConstraint = EqualType VarIndex DetType -- v ~ alpha
                   | AppliedType VarIndex VarIndex [DetType] -- v ~ y @ alpha1 ... alphan
  deriving (Eq, Ord, Show)

data DS = DS { detEnv :: DetEnv
             , localDetEnv :: DetEnv
             , tcEnv :: TCEnv
             , instEnv :: InstEnv
             , valueEnv :: ValueEnv
             , classEnv :: ClassEnv
             , moduleIdent :: ModuleIdent
             , freshIdent :: VarIndex
             }

freshVar :: DM VarIndex
freshVar = do
  i <- gets freshIdent
  modify (\s -> s { freshIdent = i + 1 })
  return i

addLocalType :: IdentInfo -> DetType -> DM ()
addLocalType ii ty = modify (\s -> s { localDetEnv = Map.insert ii ty (localDetEnv s) })

type DM = StateT DS IO

determinismCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> InstEnv
                 -> Module PredType -> IO (DetEnv, [Message])
determinismCheck mid tce ve ce ie (Module _ _ _ _ _ _ ds) = flip evalStateT initState $ do
  liftIO $ putStrLn "Determinism check"
  dsvs <- Map.fromList <$> mapM (\d -> (oneDeclIdent d,) <$> freeIdents d) definingDS
  let groups = scc (declIdents mid)
                   (\d -> Set.toList $ Map.findWithDefault Set.empty (oneDeclIdent d) dsvs)
                   definingDS
  mapM_ checkGroup groups
  env <- gets detEnv
  liftIO $ putStrLn $ prettyDetEnv env
  return (env, [])
  where
    oneDeclIdent d = case declIdents mid d of
      (ii:_) -> ii
      _ -> internalError "determinismCheck: oneDeclIdent"
    initState = DS Map.empty Map.empty tce ie ve ce mid 0
    definingDS = filter isDefiningDecl ds
    isDefiningDecl FunctionDecl {} = True
    isDefiningDecl PatternDecl {} = True
    isDefiningDecl ClassDecl {} = True
    isDefiningDecl InstanceDecl {} = True
    isDefiningDecl ExternalDecl {} = True
    isDefiningDecl _ = False

declIdents :: ModuleIdent -> Decl PredType -> [IdentInfo]
declIdents mid (FunctionDecl _ _ ident _) = [QI (qualifyWith mid ident)]
declIdents _   (PatternDecl _ pat _) = map (QI . qualify . fst3) (patternVars pat)
declIdents mid (ClassDecl _ _ _ ident _ ds) =
  concatMap (map (toClassIdent (qualifyWith mid ident)) . declIdents mid) ds
declIdents mid (InstanceDecl _ _ _ ident ty ds) =
  concatMap (map (toInstanceIdent ident ty) . declIdents mid) ds
declIdents _ _ = []

toClassIdent :: QualIdent -> IdentInfo -> IdentInfo
toClassIdent cls (QI qid) = CI cls qid
toClassIdent _ ii = ii

toInstanceIdent :: QualIdent -> InstanceType -> IdentInfo -> IdentInfo
toInstanceIdent cls ty (QI qid) = case ty of
  ConstructorType _ tc -> II cls tc qid
  _ -> internalError (show ty ++ " is not a constructor type")
toInstanceIdent _ _ ii = ii

checkGroup :: [Decl PredType] -> DM ()
checkGroup ds = do
  constraints <- Set.unions <$> (mapM checkDecl ds >>= sequence)
  res <- solveConstraints constraints
  modify (\s -> s { localDetEnv = Map.empty, detEnv = Map.union res (detEnv s),  freshIdent = 0 })
  return ()

-- registers the types of defined variables on the outer layer, creates constraints on the inner layer
checkDecl :: Decl PredType -> DM (DM (Set DetConstraint))
checkDecl d@(FunctionDecl _ _ _ eqs) = do
  mid <- gets moduleIdent
  ov <- overlaps eqs
  acts <- mapM (checkEquation ov (head $ declIdents mid d)) eqs
  return (Set.unions <$> sequence acts)
checkDecl (PatternDecl _ p rhs) = do
  v <- freshVar
  cs <- checkPat v p
  return (Set.union cs <$> checkRhsTy v rhs)
checkDecl (ClassDecl _ _ _ _ _ ds) = do
  acts <- mapM checkClassDecl ds
  return (Set.unions <$> sequence acts)
checkDecl (InstanceDecl _ _ _ _ _ ds) = do
  acts <- mapM checkInstanceDecl ds
  return (Set.unions <$> sequence acts)
checkDecl (ExternalDecl _ vs) = do
  mid <- gets moduleIdent
  mapM_ (\(Var _ i) -> let qi = qualifyWith mid i
                       in addLocalType (QI qi) (externalDetMap Map.! qi)) vs
  return $ return Set.empty
checkDecl (FreeDecl _ vs) = do
  mapM_ (\(Var _ i) -> addLocalType (QI (qualify i)) Nondet) vs
  return $ return Set.empty
checkDecl _ = return $ return Set.empty

checkEquation :: Bool -> IdentInfo -> Equation PredType -> DM (DM (Set DetConstraint))
checkEquation ov ii (Equation _ lhs rhs) = do
  (cs, ty, resvar) <- genDetType lhs
  addLocalType ii ty
  return $ do
    let cs' = if ov then Set.insert (EqualType resvar Nondet) cs else cs
    liftIO $ putStrLn "Equation"
    Set.union cs' <$> checkRhsTy resvar rhs

-- TODO: add demand on strict pat
genDetType :: Lhs PredType -> DM (Set DetConstraint, DetType, VarIndex)
genDetType (FunLhs _ _ ps) = do
  vs <- replicateM (length ps) freshVar
  res <- freshVar
  cs <- Set.unions <$> zipWithM checkPat vs ps
  return (cs, foldr (DetArrow . VarTy) (VarTy res) vs, res)
genDetType (OpLhs _ p1 _ p2) = do
  v1 <- freshVar
  v2 <- freshVar
  res <- freshVar
  cs1 <- checkPat v1 p1
  cs2 <- checkPat v2 p2
  return (Set.union cs1 cs2, DetArrow (VarTy v1) (DetArrow (VarTy v2) (VarTy res)), res)
genDetType (ApLhs _ lhs ps) = do
  (cs1, ty, res) <- genDetType lhs
  vs <- replicateM (length ps) freshVar
  cs2 <- Set.unions <$> zipWithM checkPat vs ps
  return (Set.union cs1 cs2, extendArrow ty vs, res)
  where
    extendArrow :: DetType -> [VarIndex] -> DetType
    extendArrow (DetArrow ty1 ty2) vs = DetArrow ty1 (extendArrow ty2 vs)
    extendArrow ty vs = foldr (DetArrow . VarTy) ty vs

checkPat :: VarIndex -> Pattern PredType -> DM (Set DetConstraint)
checkPat v (VariablePattern _ _ i) = do
  addLocalType (QI (qualify i)) (VarTy v)
  return Set.empty
checkPat v (ConstructorPattern _ _ _ ps) = Set.unions <$> mapM (checkPat v) ps
checkPat v (InfixPattern _ _ p1 _ p2) = Set.union <$> checkPat v p1 <*> checkPat v p2
checkPat v (ParenPattern _ p) = checkPat v p
checkPat v (RecordPattern _ _ _ fs) =
  Set.unions <$> mapM (checkPatField v) fs
checkPat v (TuplePattern _ ps) =
  Set.unions <$> mapM (checkPat v) ps
checkPat v (ListPattern _ _ ps) =
  Set.unions <$> mapM (checkPat v) ps
checkPat v (AsPattern _ i p) = do
  addLocalType (QI (qualify i)) (VarTy v)
  checkPat v p
checkPat v (LazyPattern _ p) = checkPat v p
checkPat v (FunctionPattern _ _ _ ps) = undefined
checkPat v (InfixFuncPattern _ _ p1 _ p2) = undefined
checkPat _ LiteralPattern {} = return Set.empty -- TODO overloading
checkPat _ NegativePattern {} = return Set.empty -- TODO overloading

checkPatField :: VarIndex -> Field (Pattern PredType) -> DM (Set DetConstraint)
checkPatField v (Field _ _ p) = checkPat v p

checkRhsTy :: VarIndex -> Rhs PredType -> DM (Set DetConstraint)
checkRhsTy v (SimpleRhs _ _ e ds) = do
  cs <- checkLocalDeclsTy ds
  Set.union cs <$> checkExprTy v e
checkRhsTy v (GuardedRhs _ _ gs ds) = do
  cs <-checkLocalDeclsTy ds
  Set.union cs . Set.unions <$> mapM (checkCondExprTy v) gs

checkCondExprTy :: VarIndex -> CondExpr PredType -> DM (Set DetConstraint)
checkCondExprTy v (CondExpr _ e1 e2) = do
  cs1 <- checkExprTy v e1
  cs2 <- checkExprTy v e2
  return (Set.union cs1 cs2)

checkExprTy :: VarIndex -> Expression PredType -> DM (Set DetConstraint)
checkExprTy v (Variable _ ty i) = checkVar v ty i
checkExprTy v (Typed _ e _) = checkExprTy v e
checkExprTy v (Apply _ e1 e2) = do
  v1 <- freshVar
  cs1 <- checkExprTy v1 e1
  v2 <- freshVar
  cs2 <- checkExprTy v2 e2
  return $ Set.insert (AppliedType v v1 [VarTy v2]) (Set.union cs1 cs2)
checkExprTy v (InfixApply _ e1 op e2) = do
  v1 <- freshVar
  cs1 <- checkExprTy v1 e1
  v2 <- freshVar
  cs2 <- checkExprTy v2 e2
  v3 <- freshVar
  cs3 <- checkInfixOpTy v3 op
  return $ Set.insert (AppliedType v v3 [VarTy v1, VarTy v2]) (Set.unions [cs1, cs2, cs3])
checkExprTy v (Paren _ e) = checkExprTy v e
checkExprTy v Literal {} = return (Set.singleton (EqualType v Det)) -- TODO overloading
checkExprTy v (Constructor _ (PredType _ ty) _) =
  return (Set.singleton (EqualType v (mkArrowLike ty)))
checkExprTy v (Tuple _ es) =
  Set.unions <$> mapM (checkExprTy v) es
checkExprTy v (List _ _ es) =
  Set.unions <$> mapM (checkExprTy v) es
checkExprTy v (ListCompr _ e qs) = do
  cs <- Set.unions <$> mapM (checkStmt v) qs
  Set.union cs <$> checkExprTy v e
checkExprTy v (EnumFrom _ e) = undefined
checkExprTy v (EnumFromThen _ e1 e2) = undefined
checkExprTy v (EnumFromTo _ e1 e2) = undefined
checkExprTy v (EnumFromThenTo _ e1 e2 e3) = undefined
checkExprTy v (Record _ _ _ fs) =
  Set.unions <$> mapM (checkExprField v) fs
checkExprTy v (RecordUpdate _ e fs) = do
  cs <- checkExprTy v e
  Set.union cs . Set.unions <$> mapM (checkExprField v) fs
checkExprTy v (Lambda _ ps e) = do
  vs <- replicateM (length ps) freshVar
  cs <- Set.unions <$> zipWithM checkPat vs ps
  v' <- freshVar
  let c = EqualType v (foldr (DetArrow . VarTy) (VarTy v') vs)
  Set.insert c . Set.union cs <$> checkExprTy v' e
checkExprTy v (Let _ _ ds e) = do
  cs <- checkLocalDeclsTy ds
  Set.union cs <$> checkExprTy v e
checkExprTy v (Do _ _ ss e) = do
  cs <- Set.unions <$> mapM (checkStmt v) ss
  Set.union cs <$> checkExprTy v e
checkExprTy v (LeftSection _ e op) =
  Set.union <$> checkExprTy v e <*> checkInfixOpTy v op
checkExprTy v (RightSection _ op e) =
  Set.union <$> checkInfixOpTy v op <*> checkExprTy v e
checkExprTy v (UnaryMinus _ e) =
  checkExprTy v e -- TODO overloading
checkExprTy v (IfThenElse _ e1 e2 e3) =
  Set.unions <$> mapM (checkExprTy v) [e1, e2, e3]
checkExprTy v (Case _ _ _ e bs) = undefined

checkStmt :: VarIndex -> Statement PredType -> DM (Set DetConstraint)
checkStmt _ (StmtDecl _ _ ds) = checkLocalDeclsTy ds
checkStmt v (StmtExpr _ e) = checkExprTy v e
checkStmt v (StmtBind _ p e2) =
  Set.union <$> checkPat v p <*> checkExprTy v e2

checkExprField :: VarIndex -> Field (Expression PredType) -> DM (Set DetConstraint)
checkExprField v (Field _ _ e) = checkExprTy v e

checkInfixOpTy :: VarIndex -> InfixOp PredType -> DM (Set DetConstraint)
checkInfixOpTy v (InfixOp ty i) = checkVar v ty i
checkInfixOpTy v (InfixConstr (PredType _ ty) _) =
  return (Set.singleton (EqualType v (mkArrowLike ty)))

checkVar :: VarIndex -> PredType -> QualIdent -> DM (Set DetConstraint)
checkVar v ty i = do
  ii <- variableFreeIdent i ty
  lcl <- gets localDetEnv
  ext <- gets detEnv
  case Map.lookup ii lcl of
      Just ty' -> return $ Set.singleton $ EqualType v ty'
      Nothing -> case Map.lookup ii ext of
        Just ty' -> Set.singleton . EqualType v <$> instantiate ty'
        Nothing -> internalError $ "checkVar: " ++ show i ++ " not found"

instantiate :: DetType -> DM DetType
instantiate = fmap fst . go Map.empty
  where
    go mp (VarTy v) = case Map.lookup v mp of
      Just ty -> return (ty, mp)
      Nothing -> do
        i <- freshVar
        return (VarTy i, Map.insert v (VarTy i) mp)
    go mp (DetArrow ty1 ty2) = do
      (ty1', mp') <- go mp ty1
      (ty2', mp'') <- go mp' ty2
      return (DetArrow ty1' ty2', mp'')
    go mp ty = return (ty, mp)

checkLocalDeclsTy :: [Decl PredType] -> DM (Set DetConstraint)
checkLocalDeclsTy ds = Set.unions <$> (mapM checkDecl ds >>= sequence)

checkClassDecl :: Decl PredType -> DM (DM (Set DetConstraint))
checkClassDecl = undefined

checkInstanceDecl :: Decl PredType -> DM (DM (Set DetConstraint))
checkInstanceDecl = undefined

solveConstraints :: Set DetConstraint -> DM (Map IdentInfo DetType)
solveConstraints constraints = do
  let grps = scc defs uses $ Set.toAscList constraints
  liftIO $ print grps
  let solved = foldl solveGroup Map.empty grps
  liftIO $ print solved
  lcl <- gets localDetEnv
  return $ Map.map (`subst` solved) lcl
  where
    defs (AppliedType v w _) = [v, w]
    defs (EqualType v ty) = v : vars ty
    uses (AppliedType v w ty) = v : w : concatMap vars ty
    uses (EqualType v ty) = v : vars ty
    vars (VarTy v) = [v]
    vars (DetArrow ty1 ty2) = vars ty1 ++ vars ty2
    vars _ = []

solveGroup :: Map VarIndex DetType -> [DetConstraint] -> Map VarIndex DetType
solveGroup = go Map.empty
  where
    go current solutions [] = Map.union current solutions
    go current solutions (c:cs) = case c of
      AppliedType v w tys ->
        let substTys = map (`subst` solutions) tys
        in case Map.lookup w current of
             -- applied types are always the last entries in the list,
             -- so w can only be constrained by an applied type.
             -- Thus, it is safe to leave v as-is.
             Nothing -> go current solutions cs
             Just ty -> case Map.lookup v current of
                Nothing -> go (Map.insert v (applyTy ty substTys) current) solutions cs
                Just ty' -> case unify ty' (applyTy ty substTys) current cs of
                  (new, cs') -> go (Map.insert v new current) solutions  cs'
      EqualType v ty ->
        let substTy = subst ty solutions
        in case Map.lookup v current of
          Nothing -> go (Map.insert v substTy current) solutions cs
          Just ty' -> case unify substTy ty' current cs of
            (new, cs')  -> go (Map.insert v new current) solutions cs'

    -- returns the list of old constraints and the new ones that have to hold,
    -- and the new type to be used for the variable in question
    unify :: DetType -> DetType -> Map VarIndex DetType -> [DetConstraint] -> (DetType, [DetConstraint])
    unify (VarTy v) ty current cs = case Map.lookup v current of
      Nothing -> (ty, EqualType v ty : cs)
      Just ty' -> unify ty' ty current cs
    unify ty (VarTy v) current cs = case Map.lookup v current of
      Nothing -> (ty, EqualType v ty : cs)
      Just ty' -> unify ty ty' current cs
    unify Det Det _ cs = (Det, cs)
    unify Nondet Nondet _ cs = (Nondet, cs)
    unify Nondet _ _ cs = (Nondet, cs)
    unify _ Nondet _ cs = (Nondet, cs)
    unify (DetArrow ty1 ty2) (DetArrow ty1' ty2') current cs =
      let (new1, cs1) = unify ty1 ty1' current cs
          (new2, cs2) = unify ty2 ty2' current cs1
      in (DetArrow new1 new2, cs2)
    unify ty1 ty2 _ _ = internalError $ "unify: " ++ show ty1 ++ " and " ++ show ty2 ++ " are not unifiable"

    applyTy :: DetType -> [DetType] -> DetType
    applyTy (VarTy v) _ = VarTy v
    applyTy ty [] = ty
    applyTy (DetArrow ty1 ty2) (ty:rest) = case ty `moreSpecific` ty1 of
      Just s -> applyTy (subst ty2 s) rest
      Nothing -> Nondet
    applyTy ty tys = internalError $ "applyTy: not enough arguments" ++ show ty ++ " @ " ++ show tys

    moreSpecific :: DetType -> DetType -> Maybe (Map VarIndex DetType)
    moreSpecific ty (VarTy v) = Just (Map.singleton v ty)
    moreSpecific (DetArrow ty1 ty2) (DetArrow ty1' ty2') = do
      s1 <- ty1 `lessSpecific` ty1'
      s2 <- ty2 `moreSpecific` ty2'
      return (Map.union s1 s2)
    moreSpecific Det Nondet = Just Map.empty
    moreSpecific Det Det = Just Map.empty
    moreSpecific Nondet Nondet = Just Map.empty
    moreSpecific _ _ = Nothing

    lessSpecific ty (VarTy v) = Just (Map.singleton v ty)
    lessSpecific (DetArrow ty1 ty2) (DetArrow ty1' ty2') = do
      s1 <- ty1 `moreSpecific` ty1'
      s2 <- ty2 `lessSpecific` ty2'
      return (Map.union s1 s2)
    lessSpecific Nondet Det = Just Map.empty
    lessSpecific Det Det = Just Map.empty
    lessSpecific Nondet Nondet = Just Map.empty
    lessSpecific _ _ = Nothing

subst :: DetType -> Map VarIndex DetType -> DetType
subst (VarTy v) solutions = case Map.lookup v solutions of
  Nothing -> VarTy v
  Just ty -> ty
subst (DetArrow ty1 ty2) solutions = DetArrow (subst ty1 solutions) (subst ty2 solutions)
subst ty _ = ty

overlaps :: [Equation PredType] -> DM Bool
overlaps = checkOverlap . map (getPats . void)
  where
    getPats (Equation _ lhs _) = getLhsPats lhs
    getLhsPats (FunLhs _ _ ps) = ps
    getLhsPats (OpLhs _ p1 _ p2) = [p1, p2]
    getLhsPats (ApLhs _ lhs ps) = getLhsPats lhs ++ ps

mkArrowLike :: Type -> DetType
mkArrowLike ty = case unapplyType True ty of
  (_, xs) -> foldr DetArrow (VarTy 0) $ replicate (length xs) (VarTy 0)

class DetCheck a where
  freeIdents :: a -> DM (Set IdentInfo)

instance DetCheck a => DetCheck [a] where
  freeIdents = fmap Set.unions . mapM freeIdents

instance DetCheck b => DetCheck (a, b) where
  freeIdents (_, b) = freeIdents b

instance DetCheck (Decl PredType) where
  freeIdents (ClassDecl _ _ _ _ _ ds) = freeIdents ds
  freeIdents (InstanceDecl _ _ _ _ _ ds) = freeIdents ds
  freeIdents (PatternDecl _ _ rhs) = freeIdents rhs
  freeIdents (FunctionDecl _ _ _ rhs) = freeIdents rhs
  freeIdents _ = return Set.empty

instance DetCheck (Rhs PredType) where
  freeIdents (SimpleRhs _ _ e ds) = freeIdents e `unionM` freeIdents ds
  freeIdents (GuardedRhs _ _ es ds) = freeIdents es `unionM` freeIdents ds

instance DetCheck (Equation PredType) where
  freeIdents (Equation _ _ e) = freeIdents e

instance DetCheck (Expression PredType) where
  freeIdents (Variable _ ty i) = Set.singleton <$> variableFreeIdent i ty
  freeIdents (Typed _ e _) = freeIdents e
  freeIdents (Apply _ e1 e2) = freeIdents e1 `unionM` freeIdents e2
  freeIdents (InfixApply _ e1 _ e2) = freeIdents e1 `unionM` freeIdents e2
  freeIdents (Lambda _ _ e) = freeIdents e
  freeIdents (Let _ _ ds e) = freeIdents ds `unionM` freeIdents e
  freeIdents edo@(Do _ _ ss e) = freeIdents ss `unionM` freeIdents e `unionM`
    monadFreeIdent (typeOf edo)
  freeIdents (List _ _ es) = freeIdents es
  freeIdents Constructor {} = return Set.empty
  freeIdents Literal {} = return Set.empty
  freeIdents (Tuple _ es) = freeIdents es
  freeIdents (ListCompr _ e qs) = freeIdents e `unionM` freeIdents qs
  freeIdents (EnumFrom _ e) = freeIdents e `unionM` enumFreeIdent qEnumFromId (typeOf e)
  freeIdents (EnumFromThen _ e1 e2) = freeIdents e1 `unionM` freeIdents e2 `unionM`
    enumFreeIdent qEnumFromThenId (typeOf e1)
  freeIdents (EnumFromTo _ e1 e2) = freeIdents e1 `unionM` freeIdents e2 `unionM`
    enumFreeIdent qEnumFromToId (typeOf e1)
  freeIdents (EnumFromThenTo _ e1 e2 e3) = freeIdents e1 `unionM` freeIdents e2 `unionM`
    freeIdents e3 `unionM` enumFreeIdent qEnumFromThenToId (typeOf e1)
  freeIdents (Paren _ e) = freeIdents e
  freeIdents (LeftSection _ e _) = freeIdents e
  freeIdents (RightSection _ _ e) = freeIdents e
  freeIdents (Record _ _ _ fs) = freeIdents fs
  freeIdents (RecordUpdate _ e fs) = freeIdents e `unionM` freeIdents fs
  freeIdents (UnaryMinus _ e) = freeIdents e
  freeIdents (IfThenElse _ e1 e2 e3) = freeIdents e1 `unionM` freeIdents e2 `unionM` freeIdents e3
  freeIdents (Case _ _ _ e bs) = freeIdents e `unionM` freeIdents bs

instance DetCheck (CondExpr PredType) where
  freeIdents (CondExpr _ e2 e3) = freeIdents e2 `unionM` freeIdents e3

instance DetCheck (Statement PredType) where
  freeIdents (StmtDecl _ _ ds) = freeIdents ds
  freeIdents (StmtExpr _ e) = freeIdents e
  freeIdents (StmtBind _ _ e2) = freeIdents e2

instance DetCheck (Alt PredType) where
  freeIdents (Alt _ _ rhs) = freeIdents rhs

instance DetCheck a => DetCheck (Field a) where
  freeIdents (Field _ _ e) = freeIdents e

enumFreeIdent :: QualIdent -> Type -> DM (Set IdentInfo)
enumFreeIdent q ty =
  case unapplyType True ty of
    (TypeConstructor tc, _) ->
      return (Set.singleton (II qEnumId tc q))
    _ -> internalError (show ty ++ " is not an enum type")

-- TODO MonadFail
monadFreeIdent :: Type -> DM (Set IdentInfo)
monadFreeIdent ty =
  case unapplyType True ty of
    (TypeConstructor tc, _) ->
      return (Set.singleton (II qMonadId tc qBindId))
    _ -> internalError (show ty ++ " is not an enum type")

variableFreeIdent :: QualIdent -> PredType -> DM IdentInfo
variableFreeIdent qid (PredType _ ty) = do
  vEnv <- gets valueEnv
  mid <- gets moduleIdent
  case qualLookupValueUnique mid qid vEnv of
    [Value orig ci _ _] -> case ci of
      Nothing -> return (QI orig)
      Just ci' -> case unapplyType True ty of
        (TypeConstructor tc, _) -> return (II ci' tc qid)
        _ -> internalError (show ty ++ " is not a constructor type")
    _ -> return (QI qid)

externalDetMap :: Map QualIdent DetType
externalDetMap = Map.empty

unionM :: (Ord a, Monad m) => m (Set a) -> m (Set a) -> m (Set a)
unionM = liftM2 Set.union

prettyDetEnv :: DetEnv -> String
prettyDetEnv = unlines . map prettyDetEnvEntry . Map.toList
  where
    prettyDetEnvEntry (ii, ty) = prettyII ii ++ " :: " ++ prettyTy ty

prettyII :: IdentInfo -> String
prettyII (QI qid) = render $ pPrint qid
prettyII (II cls tc meth) = render $ parens (pPrint cls <+> pPrint tc) <> dot <> pPrint meth
prettyII (CI cls meth) = render $ pPrint cls <> dot <> pPrint meth

prettyTy :: DetType -> String
prettyTy (VarTy v) = "a" ++ show v
prettyTy Det = "Det"
prettyTy Nondet = "Nondet"
prettyTy (DetArrow ty1 ty2) = prettyTy ty1 ++ " -> " ++ prettyTy ty2

checkOverlap :: [[Pattern ()]] -> DM Bool
checkOverlap pats = do
  -- 1. We simplify the patterns by removing syntactic sugar temporarily
  --    for a simpler implementation.
  simplePats <- mapM (mapM simplifyPat) pats
  -- 2. We compute overlapping pattern matching alternatives
  processEqs simplePats

-- |Simplify a 'Pattern' until it only consists of
--   * Variables
--   * Integer, Float or Char literals
--   * Constructors
-- All other patterns like as-patterns, list patterns and alike are desugared.
simplifyPat :: Pattern () -> DM (Pattern ())
simplifyPat p@(LiteralPattern        _ _ l) = return $ case l of
  String s -> simplifyListPattern $ map (LiteralPattern NoSpanInfo () . Char) s
  _        -> p
simplifyPat (NegativePattern       spi a l) =
  return $ LiteralPattern spi a (negateLit l)
  where
    negateLit (Int   n) = Int   (-n)
    negateLit (Float d) = Float (-d)
    negateLit x         = x
simplifyPat v@VariablePattern {} = return v
simplifyPat (ConstructorPattern spi a c ps) =
  ConstructorPattern spi a c <$> mapM simplifyPat ps
simplifyPat (InfixPattern    spi a p1 c p2) =
  ConstructorPattern spi a c <$> mapM simplifyPat [p1, p2]
simplifyPat (ParenPattern              _ p) = simplifyPat p
simplifyPat (RecordPattern        _ _ c fs) = do
  (_, ls) <- getAllLabels c
  let ps = map (getPattern (map field2Tuple fs)) ls
  simplifyPat (ConstructorPattern NoSpanInfo () c ps)
  where
    getPattern fs' l' =
      fromMaybe wildPat (lookup l' [(unqualify l, p) | (l, p) <- fs'])
simplifyPat (TuplePattern            _ ps) =
  ConstructorPattern NoSpanInfo () (qTupleId (length ps))
    <$> mapM simplifyPat ps
simplifyPat (ListPattern           _ _ ps) =
  simplifyListPattern <$> mapM simplifyPat ps
simplifyPat (AsPattern             _ _ p) = simplifyPat p
simplifyPat (LazyPattern             _ _) = return wildPat
simplifyPat FunctionPattern {} = return wildPat
simplifyPat InfixFuncPattern {} = return wildPat

getAllLabels :: QualIdent -> DM (QualIdent, [Ident])
getAllLabels c = do
  tyEnv <- gets valueEnv
  case qualLookupValue c tyEnv of
    [DataConstructor qc _ ls _] -> return (qc, ls)
    _                           -> internalError $
          "Checks.DeterminismCheck.getAllLabels: " ++ show c

-- |Create a simplified list pattern by applying @:@ and @[]@.
simplifyListPattern :: [Pattern ()] -> Pattern ()
simplifyListPattern =
  foldr (\p1 p2 -> ConstructorPattern NoSpanInfo () qConsId [p1, p2])
        (ConstructorPattern NoSpanInfo () qNilId [])

type EqnInfo = [Pattern ()]

-- |Compute the overlapping pattern by inspecting the first patterns and
-- categorize them as literal, constructor or variable patterns.
processEqs :: [EqnInfo] -> DM Bool
processEqs []              = return False
processEqs eqs@(ps:_)
  | null ps                = return (length eqs > 1)
  | any isLitPat firstPats = processLits eqs
  | any isConPat firstPats = processCons eqs
  | all isVarPat firstPats = processVars eqs
  | otherwise              = internalError "Checks.DeterminismCheck.processEqs"
  where firstPats = map firstPat eqs

-- |Literal patterns are checked by extracting the matched literals
processLits :: [EqnInfo] -> DM Bool
processLits = processWith processUsedLits getLit

-- |Check overlapping patterns starting with the used literals
processUsedLits :: [Literal] -> [EqnInfo]
                -> DM Bool
processUsedLits lits qs = or <$> mapM process lits
  where
    process lit = do
      let qs' = [shiftPat q | q <- qs, isVarLit lit (firstPat q)]
          ovlp = length qs' > 1
      nd <- processEqs qs'
      return (nd && ovlp)

-- |Constructor patterns are checked by extracting the matched constructors
--  and constructing a pattern for any missing case.
processCons :: [EqnInfo] -> DM Bool
processCons = processWith processUsedCons getCon

processWith :: Eq a => ([a] -> [EqnInfo] -> DM Bool) -> (Pattern () -> [a]) -> [EqnInfo] -> DM Bool
processWith process getter qs = do
  -- Compute any overlap starting with the used pattern
  nd <- process used_pats qs
  if null defaults
    then return nd
    else do
      -- Overlap for the default alternatives
      nd2 <- processEqs defaults
      return (nd || nd2)
  where
    -- used pattern
    used_pats    = nub $ concatMap (getter . firstPat) qs
    -- default alternatives (variable pattern)
    defaults     = [ shiftPat q' | q' <- qs, isVarPat (firstPat q') ]

-- |Check overlap starting with the used constructors
processUsedCons :: [(QualIdent, Int)] -> [EqnInfo]
                -> DM Bool
processUsedCons cons qs = or <$> mapM process cons
  where
    process (c, a) = do
      let qs' = [ removeFirstCon c a q | q <- qs , isVarCon c (firstPat q)]
          ovlp = length qs' > 1
      nd <- processEqs qs'
      return (nd && ovlp)

    removeFirstCon c a (p:ps)
      | isVarPat p = replicate a wildPat ++ ps
      | isCon c  p = patArgs p           ++ ps
    removeFirstCon _ _ _ = internalError "Checks.WarnCheck.removeFirstCon"

-- |Variable patterns overlap if there is more than one equation and the remaining pattern overlap
processVars :: [EqnInfo] -> DM Bool
processVars eqs = do
  let ovlp = length eqs > 1
  nd <- processEqs (map shiftPat eqs)
  return (nd && ovlp)

-- |Get the first pattern of a list.
firstPat :: EqnInfo -> Pattern ()
firstPat [] = internalError "Checks.DeterminismCheck.firstPat: empty list"
firstPat (p:_) = p

-- |Drop the first pattern of a list.
shiftPat :: EqnInfo -> EqnInfo
shiftPat [] = internalError "Checks.DeterminismCheck.shiftPat: empty list"
shiftPat (_:ps) = ps

-- |Wildcard pattern.
wildPat :: Pattern ()
wildPat = VariablePattern NoSpanInfo () anonId

-- |Retrieve any literal out of a pattern.
getLit :: Pattern a -> [Literal]
getLit (LiteralPattern _ _ l) = [l]
getLit _                      = []

-- |Retrieve the constructor name and its arity for a pattern.
getCon :: Pattern a -> [(QualIdent, Int)]
getCon (ConstructorPattern _ _ c ps) = [(c, length ps)]
getCon _                             = []

-- |Is a pattern a variable or literal pattern?
isVarLit :: Literal -> Pattern a -> Bool
isVarLit l p = isVarPat p || isLit l p

-- |Is a pattern a variable or a constructor pattern with the given constructor?
isVarCon :: QualIdent -> Pattern a -> Bool
isVarCon c p = isVarPat p || isCon c p

-- |Is a pattern a pattern matching for the given constructor?
isCon :: QualIdent -> Pattern a -> Bool
isCon c (ConstructorPattern _ _ d _) = c == d
isCon _ _                            = False

-- |Is a pattern a pattern matching for the given literal?
isLit :: Literal -> Pattern a -> Bool
isLit l (LiteralPattern _ _ m) = l == m
isLit _ _                      = False

-- |Is a pattern a literal pattern?
isLitPat :: Pattern a -> Bool
isLitPat LiteralPattern {} = True
isLitPat _                 = False

-- |Is a pattern a variable pattern?
isVarPat :: Pattern a -> Bool
isVarPat VariablePattern {} = True
isVarPat _                  = False

-- |Is a pattern a constructor pattern?
isConPat :: Pattern a -> Bool
isConPat ConstructorPattern {} = True
isConPat _                     = False

-- |Retrieve the arguments of a pattern.
patArgs :: Pattern a -> [Pattern a]
patArgs (ConstructorPattern _ _ _ ps) = ps
patArgs _                             = []
