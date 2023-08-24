{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
module Checks.DeterminismCheck (determinismCheck, DetEnv) where

import Prelude hiding ( (<>) )
import Control.Arrow ( second )
import Control.Monad.State
import Data.List ( nub, intercalate )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( fromMaybe )
import Data.Set ( Set )
import qualified Data.Set as Set

import Base.Messages ( Message, internalError )
import Base.SCC ( scc )
import Base.Types
import Base.TypeSubst ( idSubst, SubstType(subst) )
import Base.Typing ( patternVars, Typeable(typeOf), matchType )
import Base.Utils ( fst3 )
import Curry.Base.Ident
import Curry.Base.Pretty ( pPrint, dot, (<+>), (<>), parens, render, text )
import Curry.Base.SpanInfo ( SpanInfo(NoSpanInfo) )
import Curry.Syntax.Type
import Curry.Syntax.Utils ( field2Tuple )
import Env.Class ( ClassEnv, lookupClassInfo, classMethods )
import Env.Instance ( InstEnv )
import Env.TypeConstructor ( TCEnv )
import Env.Value ( qualLookupValue, qualLookupValueUnique, ValueInfo(..), ValueEnv )

import Debug.Trace

type DetEnv = Map IdentInfo DetScheme
type TopDetEnv = DetEnv
data NestDetEnv = Top TopDetEnv
                | LocalEnv NestDetEnv DetEnv

data IdentInfo = QI QualIdent
               | II QualIdent QualIdent QualIdent -- class, tycon, method (only for known instances with the given type constructor)
               | LII QualIdent Type QualIdent -- class, inst type, method (only for locally bound instances from a constraint)
               | CI QualIdent QualIdent -- class, default method
  deriving (Eq, Ord, Show)

bindNestEnv :: IdentInfo -> DetScheme -> NestDetEnv -> NestDetEnv
bindNestEnv ii ty (Top env) = Top (Map.insert ii ty env)
bindNestEnv ii ty (LocalEnv inner lcl) = LocalEnv inner (Map.insert ii ty lcl)

nestEnv :: NestDetEnv -> NestDetEnv
nestEnv env = LocalEnv env Map.empty

unnestEnv :: NestDetEnv -> NestDetEnv
unnestEnv (Top env) = Top env
unnestEnv (LocalEnv env _) = env

extractTopEnv :: NestDetEnv -> TopDetEnv
extractTopEnv (Top env) = env
extractTopEnv (LocalEnv env _) = extractTopEnv env

lookupNestEnv :: IdentInfo -> NestDetEnv -> Maybe DetScheme
lookupNestEnv ii (Top env) = Map.lookup ii env
lookupNestEnv ii (LocalEnv env lcl) = case Map.lookup ii lcl of
  Just ty -> Just ty
  Nothing -> lookupNestEnv ii env

mapNestEnv :: (DetScheme -> DetScheme) -> NestDetEnv -> NestDetEnv
mapNestEnv f (Top env) = Top (Map.map f env)
mapNestEnv f (LocalEnv env lcl) = LocalEnv (mapNestEnv f env) (Map.map f lcl)

flattenNestEnv :: NestDetEnv -> DetEnv
flattenNestEnv (Top env) = env
flattenNestEnv (LocalEnv env lcl) = Map.union lcl (flattenNestEnv env)

type VarIndex = Int

data DetType = VarTy VarIndex
             | Det
             | DetArrow DetType DetType
             | Nondet
  deriving (Eq, Ord, Show)

data DetConstraint = EqualType VarIndex DetType -- v ~ alpha
                   | AppliedType VarIndex VarIndex [DetType] -- v ~ y @ alpha1 ... alphan
  deriving (Eq, Ord, Show)

data DetScheme = Forall [VarIndex] DetType
  deriving (Eq, Ord, Show)

toSchema :: DetType -> DetScheme
toSchema = Forall []

data DS = DS { detEnv :: TopDetEnv
             , localDetEnv :: NestDetEnv
             , valueEnv :: ValueEnv
             , classEnv :: ClassEnv
             , instanceEnv :: InstEnv
             , moduleIdent :: ModuleIdent
             , freshIdent :: VarIndex
             }

freshVar :: DM VarIndex
freshVar = do
  i <- gets freshIdent
  modify (\s -> s { freshIdent = i + 1 })
  return i

addLocalType :: IdentInfo -> DetScheme -> DM ()
addLocalType ii ty = do
  liftIO $ putStrLn $ "Adding local type " ++ prettyII ii ++ " with " ++ prettyScheme ty
  modify (\s -> s { localDetEnv = bindNestEnv ii ty (localDetEnv s) })

type DM = StateT DS IO

enterScope :: DM ()
enterScope = modify (\s -> s { localDetEnv = nestEnv (localDetEnv s) })

exitScope :: DM ()
exitScope = modify (\s -> s { localDetEnv = unnestEnv (localDetEnv s) })

scoped :: DM a -> DM a
scoped act = do
  enterScope
  res <- act
  exitScope
  return res

determinismCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> InstEnv
                 -> Module PredType -> IO (DetEnv, [Message])
determinismCheck mid _tce ve ce ie (Module _ _ _ _ _ _ ds) = flip evalStateT initState $ do
  liftIO $ putStrLn "Determinism check"
  dsvs <- Map.fromList <$> mapM (\d -> (oneDeclIdent d,) <$> freeIdents d) definingDS
  liftIO $ putStrLn $ prettyList (\(i, is) -> prettyII i ++ " uses " ++ prettyList prettyII (Set.toList is))
                                  (Map.toList dsvs)
  let groups = scc (declIdents mid)
                   (\d -> Set.toList $ Map.findWithDefault Set.empty (oneDeclIdent d) dsvs)
                   definingDS
  liftIO $ putStrLn $ prettyList (prettyList prettyII) (map (concatMap (declIdents mid)) groups)
  mapM_ checkGroup groups
  env <- gets detEnv
  liftIO $ putStrLn $ prettyDetEnv env
  return (env, [])
  where
    oneDeclIdent d = case declIdents mid d of
      (ii:_) -> ii
      _ -> internalError $ "DeterminismCheck.oneDeclIdent: " ++ show d
    initState = DS Map.empty (Top Map.empty) ve ce ie mid 0
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

zeroUniqueQual :: QualIdent -> QualIdent
zeroUniqueQual qi = qi { qidIdent = (qidIdent qi) { idUnique = 0 } }

toInstanceIdent :: QualIdent -> InstanceType -> IdentInfo -> IdentInfo
toInstanceIdent cls ty (QI qid) = case ty of
  ConstructorType _ tc -> II qcls qtc (zeroUniqueQual qid)
    where
      qcls | isQualified cls = cls
           | otherwise       = qualifyLike qid (unqualify cls)
      qtc  | isQualified tc  = tc
           | otherwise       = qualifyLike qid (unqualify tc)
  _ -> internalError (show ty ++ " is not a constructor type")
toInstanceIdent _ _ ii = ii

checkGroup :: [Decl PredType] -> DM ()
checkGroup ds = do
  constraints <- Set.unions <$> (mapM checkDecl ds >>= sequence)
  res <- Map.map abstract . extractTopEnv <$> solveConstraints constraints
  modify (\s -> s { localDetEnv = Top Map.empty, detEnv = Map.union res (detEnv s),  freshIdent = 0 })
  return ()

-- registers the types of defined variables on the outer layer, creates constraints on the inner layer
checkDecl :: Decl PredType -> DM (DM (Set DetConstraint))
checkDecl d@(FunctionDecl _ (PredType preds fty) _ eqs) = do
  mid <- gets moduleIdent
  checkFun preds fty (declIdents mid d) eqs
checkDecl (PatternDecl _ p rhs) = do
  v <- freshVar
  (cs, _) <- checkPat v p
  return (Set.union cs <$> scoped (checkRhsTy v rhs))
checkDecl (ClassDecl _ _ _ cls _ ds) = do
  acts <- mapM (checkClassDecl cls) ds
  return (Set.unions <$> sequence acts)
checkDecl (InstanceDecl _ _ _ cls ty ds) = do
  acts <- mapM (checkInstanceDecl cls ty) ds
  return (Set.unions <$> sequence acts)
checkDecl (ExternalDecl _ vs) = do
  mid <- gets moduleIdent
  mapM_ (\(Var _ i) -> let qi = qualifyWith mid i
                       in addLocalType (QI qi) (externalDetMap Map.! qi)) vs
  return $ return Set.empty
checkDecl (FreeDecl _ vs) = do
  mapM_ (\(Var _ i) -> addLocalType (QI (qualify i)) (toSchema Nondet)) vs
  return $ return Set.empty
checkDecl _ = return $ return Set.empty

checkFun :: PredSet -> Type -> [IdentInfo] -> [Equation PredType] -> DM (DM (Set DetConstraint))
checkFun _ _ _ [] = internalError "DeterminismCheck.checkDecl: empty function"
checkFun preds fty is eqs@(e:_) = do
  let lhsArity OpLhs {} = 2
      lhsArity (FunLhs _ _ ps) = length ps
      lhsArity (ApLhs _ lhs ps) = lhsArity lhs + length ps
      arity = case e of Equation _ lhs _ -> lhsArity lhs
  ov <- overlaps eqs
  args <- replicateM arity freshVar
  res <- freshVar
  mapM_ (`addLocalType` toSchema (foldr (DetArrow . VarTy) (VarTy res) args)) is
  return $ scoped $ do
    clsEnv <- gets classEnv
    mid <- gets moduleIdent
    vEnv <- gets valueEnv
    let tySubst = matchType fty (typeOf eqs) idSubst
        addPred (Pred cls' instty) =
          let addMeth i = case qualLookupValueUnique mid (qualifyLike cls' i) vEnv of
                [Value q _ _ (ForAll _ (PredType _ t))] -> addLocalType (LII cls' instty q) (mkArrowLike t)
                _ -> internalError $ "checkInstanceDecl: " ++ show (cls', i) ++ " not found"
          in mapM_ addMeth (classMethods cls' clsEnv)
        c = if ov then Set.singleton (EqualType res Nondet) else Set.empty
    mapM_ (addPred . subst tySubst) preds
    Set.union c . Set.unions <$> mapM (checkEquation args res) eqs

checkEquation :: [VarIndex] -> VarIndex -> Equation PredType -> DM (Set DetConstraint)
checkEquation args res (Equation _ lhs rhs) = do
  (cs, is) <- genDetType args lhs
  let demands = foldr (Set.insert . EqualType res . VarTy) Set.empty is -- for all demanded variables: res ~ alpha
  Set.union demands . Set.union cs <$> scoped (checkRhsTy res rhs)

-- Returns a set of constraints and a list of variables that are demanded strictly
genDetType :: [VarIndex] -> Lhs PredType -> DM (Set DetConstraint, [VarIndex])
genDetType vs (FunLhs _ _ ps) = do
  (css, stricts) <- unzip <$> zipWithM checkPat vs ps
  return (Set.unions css, map fst $ filter snd $ zip vs stricts)
genDetType [v1, v2] (OpLhs _ p1 _ p2) = do
  (cs1, s1) <- checkPat v1 p1
  (cs2, s2) <- checkPat v2 p2
  return (Set.union cs1 cs2, map fst $ filter snd [(v1, s1), (v2, s2)])
genDetType _ OpLhs {} = internalError "DeterminismCheck.genDetType: op with more than two arguments"
genDetType vs (ApLhs _ lhs ps) = do
  let (vs1, vs2) = splitAt (length vs - length ps) vs
  (cs1, s1) <- genDetType vs1 lhs
  (cs2, s2) <- unzip <$> zipWithM checkPat vs2 ps
  return (Set.union cs1 (Set.unions cs2), s1 ++ map fst (filter snd (zip vs2 s2)))

checkPat :: VarIndex -> Pattern PredType -> DM (Set DetConstraint, Bool)
checkPat v (VariablePattern _ _ i) = do
  addLocalType (QI (qualify i)) (toSchema (VarTy v))
  return (Set.empty, False)
checkPat v (ConstructorPattern _ _ _ ps) = (,True) . Set.unions <$> mapM (fmap fst . checkPat v) ps
checkPat v (InfixPattern _ _ p1 _ p2) = ((,True) .) . Set.union <$> fmap fst (checkPat v p1) <*> fmap fst (checkPat v p2)
checkPat v (ParenPattern _ p) = checkPat v p
checkPat v (RecordPattern _ _ _ fs) =
  (,True) . Set.unions <$> mapM (checkPatField v) fs
checkPat v (TuplePattern _ ps) =
  (,True) . Set.unions <$> mapM (fmap fst . checkPat v) ps
checkPat v (ListPattern _ _ ps) =
  (,True) . Set.unions <$> mapM (fmap fst . checkPat v) ps
checkPat v (AsPattern _ i p) = do
  addLocalType (QI (qualify i)) (toSchema (VarTy v))
  checkPat v p
checkPat v (LazyPattern _ p) = second (const False) <$> checkPat v p
checkPat v (FunctionPattern _ ty i ps) = do
  w <- freshVar
  vs <- replicateM (length ps) freshVar
  let c1 = AppliedType v w (map VarTy vs)
  let c2 = EqualType w (foldr (DetArrow . VarTy) (VarTy v) vs)
  cs1 <- checkVar w ty i
  cs2 <- Set.unions . map fst <$> zipWithM checkPat vs ps
  return (Set.insert c1 (Set.insert c2 (Set.union cs1 cs2)), True) -- assumed to be demanded
checkPat v (InfixFuncPattern _ ty p1 i p2) = do
  w <- freshVar
  vs <- replicateM 2 freshVar
  let c1 = AppliedType v w (map VarTy vs)
  let c2 = EqualType w (foldr (DetArrow . VarTy) (VarTy v) vs)
  cs1 <- checkVar w ty i
  cs2 <- Set.unions . map fst <$> zipWithM checkPat vs [p1, p2]
  return (Set.insert c1 (Set.insert c2 (Set.union cs1 cs2)), True) -- assumed to be demanded
checkPat _ LiteralPattern {} = return (Set.empty, True) -- TODO overloading
checkPat _ NegativePattern {} = return (Set.empty, True) -- TODO overloading

checkPatField :: VarIndex -> Field (Pattern PredType) -> DM (Set DetConstraint)
checkPatField v (Field _ _ p) = fst <$> checkPat v p

checkRhsTy :: VarIndex -> Rhs PredType -> DM (Set DetConstraint)
checkRhsTy v (SimpleRhs _ _ e ds) = do
  cs <- checkLocalDeclsTy ds
  Set.union cs <$> scoped (checkExprTy v e)
checkRhsTy v (GuardedRhs _ _ gs ds) = do
  cs <- checkLocalDeclsTy ds
  Set.union cs . Set.unions <$> mapM (scoped . checkCondExprTy v) gs

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
  let c1 = AppliedType v v1 [VarTy v2]
      c2 = EqualType v1 (DetArrow (VarTy v2) (VarTy v))
  return $ Set.insert c1 (Set.insert c2 (Set.union cs1 cs2))
checkExprTy v (InfixApply _ e1 op e2) = do
  v1 <- freshVar
  cs1 <- checkExprTy v1 e1
  v2 <- freshVar
  cs2 <- checkExprTy v2 e2
  v3 <- freshVar
  cs3 <- checkInfixOpTy v3 op
  let c1 = AppliedType v v3 [VarTy v1, VarTy v2]
      c2 = EqualType v3 (DetArrow (VarTy v1) (DetArrow (VarTy v2) (VarTy v)))
  return $ Set.insert c1 (Set.insert c2 (Set.unions [cs1, cs2, cs3]))
checkExprTy v (Paren _ e) = checkExprTy v e
checkExprTy v Literal {} = return (Set.singleton (EqualType v Det)) -- TODO overloading
checkExprTy v (Constructor _ (PredType _ ty) _) = do
  sc <- instantiate (mkArrowLike ty)
  return (Set.singleton (EqualType v sc))
checkExprTy v (Tuple _ es) =
  Set.unions <$> mapM (checkExprTy v) es
checkExprTy v (List _ _ es) =
  Set.unions <$> mapM (checkExprTy v) es
checkExprTy v (ListCompr _ e qs) = do
  cs <- Set.unions <$> mapM (checkStmt v) qs -- TODO mapping not ok
  Set.union cs <$> checkExprTy v e
checkExprTy v (EnumFrom _ e) =
  checkExprTy v e -- TODO overloading
checkExprTy v (EnumFromThen _ e1 e2) =
  Set.union <$> checkExprTy v e1 <*> checkExprTy v e2 -- TODO overloading
checkExprTy v (EnumFromTo _ e1 e2) =
  Set.union <$> checkExprTy v e1 <*> checkExprTy v e2 -- TODO overloading
checkExprTy v (EnumFromThenTo _ e1 e2 e3) =
  Set.unions <$> mapM (checkExprTy v) [e1, e2, e3] -- TODO overloading
checkExprTy v (Record _ _ _ fs) =
  Set.unions <$> mapM (checkExprField v) fs
checkExprTy v (RecordUpdate _ e fs) = do
  cs <- checkExprTy v e
  Set.union cs . Set.unions <$> mapM (checkExprField v) fs
checkExprTy v (Lambda _ ps e) = scoped $ do
  vs <- replicateM (length ps) freshVar
  (cs, stricts) <- unzip <$> zipWithM checkPat vs ps
  v' <- freshVar
  let c = EqualType v (foldr (DetArrow . VarTy) (VarTy v') vs)
      cs' = foldr ((Set.insert . EqualType v' . VarTy) . fst) (Set.insert c (Set.unions cs)) (filter snd $ zip vs stricts)
  Set.union cs' <$> checkExprTy v' e
checkExprTy v (Let _ _ ds e) = scoped $ do
  cs <- checkLocalDeclsTy ds
  Set.union cs <$> checkExprTy v e
checkExprTy v (Do _ _ ss e) = do
  cs <- Set.unions <$> mapM (checkStmt v) ss
  Set.union cs <$> checkExprTy v e
checkExprTy v (LeftSection _ e op) = do
  v1 <- freshVar
  cs1 <- checkExprTy v1 e
  v2 <- freshVar
  v3 <- freshVar
  cs3 <- checkInfixOpTy v3 op
  let c1 = AppliedType v v3 [VarTy v1, VarTy v2]
      c2 = EqualType v3 (DetArrow (VarTy v1) (DetArrow (VarTy v2) (VarTy v)))
  return $ Set.insert c1 (Set.insert c2 (Set.unions [cs1, cs3]))
checkExprTy v (RightSection _ op e) = do
  v1 <- freshVar
  v2 <- freshVar
  cs2 <- checkExprTy v2 e
  v3 <- freshVar
  cs3 <- checkInfixOpTy v3 op
  let c1 = AppliedType v v3 [VarTy v1, VarTy v2]
      c2 = EqualType v3 (DetArrow (VarTy v1) (DetArrow (VarTy v2) (VarTy v)))
  return $ Set.insert c1 (Set.insert c2 (Set.unions [cs2, cs3]))
checkExprTy v (UnaryMinus _ e) =
  checkExprTy v e -- TODO overloading
checkExprTy v (IfThenElse _ e1 e2 e3) =
  Set.unions <$> mapM (checkExprTy v) [e1, e2, e3]
checkExprTy v (Case _ _ _ e bs) = do
  cs <- checkExprTy v e
  Set.unions . (cs:) <$> mapM (scoped . checkAlt v) bs

checkAlt :: VarIndex -> Alt PredType -> DM (Set DetConstraint)
checkAlt v (Alt _ p rhs) = do
  cs <- fst <$> checkPat v p
  Set.union cs <$> checkRhsTy v rhs

-- TODO scoping, do not check in parallel
checkStmt :: VarIndex -> Statement PredType -> DM (Set DetConstraint)
checkStmt _ (StmtDecl _ _ ds) = checkLocalDeclsTy ds
checkStmt v (StmtExpr _ e) = checkExprTy v e
checkStmt v (StmtBind _ p e2) = do
  Set.union <$> fmap fst (checkPat v p) <*> checkExprTy v e2

checkExprField :: VarIndex -> Field (Expression PredType) -> DM (Set DetConstraint)
checkExprField v (Field _ _ e) = checkExprTy v e

checkInfixOpTy :: VarIndex -> InfixOp PredType -> DM (Set DetConstraint)
checkInfixOpTy v (InfixOp ty i) = checkVar v ty i
checkInfixOpTy v (InfixConstr (PredType _ ty) _) = do
  sc <- instantiate (mkArrowLike ty)
  return (Set.singleton (EqualType v sc))

checkVar :: VarIndex -> PredType -> QualIdent -> DM (Set DetConstraint)
checkVar v (PredType _ ty) i = do
  mii <- variableFreeIdent i ty
  vEnv <- gets valueEnv
  mid <- gets moduleIdent
  let preds = case qualLookupValueUnique mid i vEnv of
        [Value _ Nothing _ (ForAll _ (PredType preds' ty'))] ->
          subst (matchType ty' ty idSubst) preds'
        _ -> emptyPredSet
  detCtx <- andM checkPred (Set.toList preds)
  case mii of
    Nothing -> return $ Set.singleton $ EqualType v Nondet
    Just ii -> do -- TODO might have a context
      lcl <- gets localDetEnv
      ext <- gets detEnv
      case lookupNestEnv ii lcl of
          Just ty'
            | detCtx    -> Set.singleton . EqualType v <$> instantiate ty'
            | otherwise -> return $ Set.singleton $ EqualType v Nondet
          Nothing -> case Map.lookup ii ext of
            Just ty'
              | detCtx -> Set.singleton . EqualType v <$> instantiate ty'
              | otherwise -> return $ Set.singleton $ EqualType v Nondet
            Nothing -> internalError $ "checkVar: " ++ prettyII ii ++ " not found in " ++ prettyDetEnv (Map.union ext (flattenNestEnv lcl))

andM :: (Foldable t, Monad m) => (a -> m Bool) -> t a -> m Bool
andM f = foldr (\a b -> f a >>= \a' -> if a' then b else return False) (return True)

checkPred :: Pred -> DM Bool
checkPred (Pred cls ty) = do
  mid <- gets moduleIdent
  clsEnv <- gets classEnv
  lcl <- gets localDetEnv
  ext <- gets detEnv
  case lookupClassInfo (qualQualify mid cls) clsEnv of
    Nothing -> internalError $ "checkPred: " ++ render (pPrint cls) ++ " not found"
    Just (_, meths) -> flip andM meths $ \(m, _) ->
      case unapplyType True ty of
        (TypeConstructor tc, _) ->
          let qtc | isQualified tc = tc
                  | otherwise      = qualifyWith mid (unqualify tc)
              ii = II (qualQualify mid cls) qtc (zeroUniqueQual (qualifyWith mid m))
          in case lookupNestEnv ii lcl of
            Just sc -> return (notNondet sc)
            Nothing -> case Map.lookup ii ext of
              Just sc -> return (notNondet sc)
              Nothing -> internalError $ "checkPred: " ++ show ii ++ " not found in " ++ prettyDetEnv (Map.union ext (flattenNestEnv lcl))
        _ ->
          let lii = LII (qualQualify mid cls) ty (zeroUniqueQual (qualifyWith mid m))
          in case lookupNestEnv lii lcl of
            Just sc -> return (notNondet sc)
            Nothing -> internalError $ "checkPred: " ++ prettyII lii ++ " not found in " ++ prettyDetEnv (flattenNestEnv lcl)

notNondet :: DetScheme -> Bool
notNondet (Forall _ ty) = notNondetTy ty

notNondetTy :: DetType -> Bool
notNondetTy (VarTy _) = True
notNondetTy Det = True
notNondetTy (DetArrow ty1 ty2) = notNondetTy ty1 && notNondetTy ty2
notNondetTy Nondet = False

instantiate :: DetScheme -> DM DetType
instantiate (Forall vs ty) = do
  vs' <- replicateM (length vs) freshVar
  return (substDetTy ty (Map.fromList (zipWith (\a -> (a,) . VarTy) vs vs')))

abstract :: DetScheme -> DetScheme
abstract (Forall _ ty) = Forall (nub (vars ty)) ty

checkLocalDeclsTy :: [Decl PredType] -> DM (Set DetConstraint)
checkLocalDeclsTy ds = Set.unions <$> (mapM checkDecl ds >>= sequence)

checkClassDecl :: Ident -> Decl PredType -> DM (DM (Set DetConstraint))
checkClassDecl cls d@(FunctionDecl _ (PredType ps fty) _ eqs) = do
  mid <- gets moduleIdent
  vEnv <- gets valueEnv
  clsEnv <- gets classEnv
  let tySubst = matchType fty (typeOf eqs) idSubst
      clsTy = case Set.toList ps of
                [Pred _ ty] -> subst tySubst ty
                _ -> internalError $ "checkClassDecl: " ++ show ps ++ " is not a single class constraint"
  case lookupClassInfo (qualifyWith mid cls) clsEnv of
    Nothing -> internalError $ "checkClassDecl: " ++ show cls ++ " not found"
    Just (_, meths) -> do
        -- Add class method `d` on global scope (happens in outer layer of checkFun)
        let is = map (toClassIdent (qualifyWith mid cls)) (declIdents mid d)
        act <- checkFun emptyPredSet fty is eqs
        return $ scoped $ do
          -- Add an instance (i.e. all methods) of the class `cls` on local scope
          -- for the type variable used in the instantiated function type.
          -- Required since a default implementation has an implicit class constraint.
          mapM_ (add . fst) meths
          act
      where
        add i = do
          case qualLookupValueUnique mid (qualifyWith mid i) vEnv of
            [Value _ _ _ (ForAll _ (PredType _ t))]
              -> addLocalType (LII (qualifyWith mid cls) clsTy (qualifyWith mid i)) (mkArrowLike t)
            _ -> internalError $ "checkClassDecl: " ++ show (cls, i) ++ " not found"
checkClassDecl _ _ = return $ return Set.empty

checkInstanceDecl :: QualIdent -> InstanceType -> Decl PredType -> DM (DM (Set DetConstraint))
checkInstanceDecl cls ty d@(FunctionDecl _ (PredType ps fty) _ eqs) = do
  -- similar to class default methods, except that the constraints are not the class constraints,
  -- but the constraints from the instance's context
  mid <- gets moduleIdent
  let is = map (toInstanceIdent (qualQualify mid cls) ty) (declIdents mid d)
  act <- checkFun ps fty is eqs
  return $ scoped act
checkInstanceDecl _ _ _ = return $ return Set.empty

solveConstraints :: Set DetConstraint -> DM NestDetEnv
solveConstraints constraints = do
  let grps = scc defs uses $ Set.toAscList constraints
  liftIO $ print grps
  let solved = foldl solveGroup Map.empty grps
  liftIO $ print solved
  lcl <- gets localDetEnv
  return $ mapNestEnv (`substDetSchema` solved) lcl
  where
    defs (AppliedType v w _) = [v, w]
    defs (EqualType v ty) = v : vars ty
    uses (AppliedType v w ty) = v : w : concatMap vars ty
    uses (EqualType v ty) = v : vars ty

vars :: DetType -> [VarIndex]
vars (VarTy v) = [v]
vars (DetArrow ty1 ty2) = vars ty1 ++ vars ty2
vars _ = []

solveGroup :: Map VarIndex DetType -> [DetConstraint] -> Map VarIndex DetType
solveGroup solutions = go Map.empty . map (`substCon` solutions)
  where
    go current [] = Map.union current solutions
    go current (c:cs) = traceShow (current, c) $ case c of
      AppliedType v w tys ->
        case Map.lookup w current of
          -- applied types are always the last entries in the list,
          -- so w can only be constrained by an applied type.
          Nothing -> go current cs
          Just ty -> case Map.lookup v current of
            Nothing -> go (Map.insert v (applyTy ty tys) current) cs
            Just ty' -> traceShow (ty, ty', applyTy ty tys) $ case unify ty' (applyTy ty tys) current cs of
              (new, cs') -> go (Map.insert v new current)  cs' -- TODO: Might fail if v has been equated to Det already and application is Nondet
      EqualType v ty
        | ty == VarTy v -> go current cs
        | v `elem` vars ty -> go (Map.insert v Nondet current) cs
        | otherwise ->
          case Map.lookup v current of
            Nothing ->
              let new = Map.singleton v ty
              in go (Map.insert v ty (Map.map (`substDetTy` new) current)) (map (`substCon` new) cs)
            Just ty' -> case unify ty ty' current cs of
              (newTy, cs')  ->
                let new = Map.singleton v newTy
                in go (Map.insert v newTy (Map.map (`substDetTy` new) current)) (map (`substCon` new) cs')

    -- returns the combined list of old constraints and the new ones that have to hold,
    -- and the new type to be used for the variable in question
    unify :: DetType -> DetType -> Map VarIndex DetType -> [DetConstraint] -> (DetType, [DetConstraint])
    unify (VarTy v) (VarTy w) _ cs | v == w = (VarTy v, cs)
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
    applyTy ty [] = ty
    applyTy Nondet _ = Nondet
    applyTy (DetArrow ty1 ty2) (ty:rest) = case ty `moreSpecific` ty1 of
      Just s -> applyTy (substDetTy ty2 s) rest
      Nothing -> Nondet
    applyTy ty tys = internalError $ "applyTy: not enough arguments " ++ show ty ++ " @ " ++ show tys

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

substDetSchema :: DetScheme -> Map VarIndex DetType -> DetScheme
substDetSchema (Forall vs ty) solutions = Forall vs (substDetTy ty (foldr Map.delete solutions vs))

substDetTy :: DetType -> Map VarIndex DetType -> DetType
substDetTy (VarTy v) solutions = case Map.lookup v solutions of
  Nothing -> VarTy v
  Just ty -> ty
substDetTy (DetArrow ty1 ty2) solutions = DetArrow (substDetTy ty1 solutions) (substDetTy ty2 solutions)
substDetTy ty _ = ty

substCon :: DetConstraint -> Map VarIndex DetType -> DetConstraint
substCon (EqualType v t) mp = EqualType v (substDetTy t mp)
substCon (AppliedType v w ts) mp = AppliedType v w (map (`substDetTy` mp) ts)

overlaps :: [Equation PredType] -> DM Bool
overlaps = checkOverlap . map (getPats . void)
  where
    getPats (Equation _ lhs _) = getLhsPats lhs
    getLhsPats (FunLhs _ _ ps) = ps
    getLhsPats (OpLhs _ p1 _ p2) = [p1, p2]
    getLhsPats (ApLhs _ lhs ps) = getLhsPats lhs ++ ps

mkArrowLike :: Type -> DetScheme
mkArrowLike ty = case unapplyType True ty of
  (_, xs) -> Forall [0] $ foldr DetArrow (VarTy 0) $ replicate (length xs) (VarTy 0)

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
  freeIdents (Variable _ (PredType _ ty) i) = maybe Set.empty Set.singleton <$> variableFreeIdent i ty
  freeIdents (Typed _ e _) = freeIdents e
  freeIdents (Apply _ e1 e2) = freeIdents e1 `unionM` freeIdents e2
  freeIdents (InfixApply _ e1 op e2) =
    freeIdents e1 `unionM` freeIdents e2 `unionM` freeIdents op
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
  freeIdents (LeftSection _ e op) = freeIdents e `unionM` freeIdents op
  freeIdents (RightSection _ op e) = freeIdents op `unionM` freeIdents e
  freeIdents (Record _ _ _ fs) = freeIdents fs
  freeIdents (RecordUpdate _ e fs) = freeIdents e `unionM` freeIdents fs
  freeIdents (UnaryMinus _ e) = freeIdents e
  freeIdents (IfThenElse _ e1 e2 e3) = freeIdents e1 `unionM` freeIdents e2 `unionM` freeIdents e3
  freeIdents (Case _ _ _ e bs) = freeIdents e `unionM` freeIdents bs

instance DetCheck (InfixOp PredType) where
  freeIdents (InfixOp (PredType _ ty) i) = maybe Set.empty Set.singleton <$> variableFreeIdent i ty
  freeIdents (InfixConstr _ _) = return Set.empty

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

variableFreeIdent :: QualIdent -> Type -> DM (Maybe IdentInfo)
variableFreeIdent qid ty = do
  vEnv <- gets valueEnv
  mid <- gets moduleIdent
  case qualLookupValueUnique mid qid vEnv of
    [Value orig ci _ _] -> case ci of
      Nothing -> return (Just (QI (qualQualify mid orig)))
      Just ci' -> case unapplyType True ty of
        (TypeConstructor tc, _) -> return (Just (II (qualQualify mid ci') tc (zeroUniqueQual (qualQualify mid orig))))
        _ -> return (Just (LII (qualQualify mid ci') ty (qualQualify mid orig)))
    _ -> return (Just (QI qid))

externalDetMap :: Map QualIdent DetScheme
externalDetMap = Map.empty

unionM :: (Ord a, Monad m) => m (Set a) -> m (Set a) -> m (Set a)
unionM = liftM2 Set.union

prettyDetEnv :: DetEnv -> String
prettyDetEnv = unlines . map prettyDetEnvEntry . Map.toList
  where
    prettyDetEnvEntry (ii, ty) = prettyII ii ++ " :: " ++ prettyScheme ty

prettyII :: IdentInfo -> String
prettyII (QI qid) = render $ pPrint qid
prettyII (II cls tc meth) = render $ parens (pPrint cls <+> pPrint tc) <> dot <> pPrint meth
prettyII (LII cls ty meth) = render $ parens (pPrint cls <+> text "@" <> pPrint ty) <> dot <> pPrint meth
prettyII (CI cls meth) = render $ pPrint cls <> dot <> pPrint meth

prettyList :: (a -> String) -> [a] -> String
prettyList f xs = "[" ++ intercalate ", " (map f xs) ++ "]"

prettyScheme :: DetScheme -> String
prettyScheme (Forall [] ty) = prettyTy ty
prettyScheme (Forall vs ty) = "forall " ++ unwords (map (prettyTy . VarTy) vs) ++ ". " ++ prettyTy ty

prettyTy :: DetType -> String
prettyTy (VarTy v) = "a" ++ show v
prettyTy Det = "Det"
prettyTy Nondet = "Nondet"
prettyTy (DetArrow ty1 ty2) = case ty1 of
  DetArrow _ _ -> "(" ++ prettyTy ty1 ++ ") -> " ++ prettyTy ty2
  _            -> prettyTy ty1 ++ " -> " ++ prettyTy ty2

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
