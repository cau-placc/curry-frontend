{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
{- TODO -}
-- TODO: Add sig to prelude
-- TODO language extension?
module Checks.DeterminismCheck (determinismCheck, DetEnv) where

import Prelude hiding ( (<>) )
import Control.Arrow ( second )
import Control.Monad ( liftM2, void, zipWithM, replicateM, forM_, foldM )
import Control.Monad.Extra ( concatMapM )
import Control.Monad.State ( evalStateT, modify, gets, liftIO, StateT )
import Data.List ( nub, (\\), find )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as Set

import Base.Messages ( Message, internalError, spanInfoMessage )
import Base.SCC ( scc )
import Base.Types
import Base.TypeSubst ( idSubst, subst )
import Base.Typing ( patternVars, typeOf, matchType )
import Base.Utils ( fst3 )
import Checks.TypeCheck ( checkFailablePattern )
import Curry.Base.Ident
import Curry.Base.Pretty ( pPrint, render, vcat, text, (<+>), (<>), colon )
import Curry.Base.SpanInfo ( SpanInfo(..), HasSpanInfo (..) )
import Curry.Syntax.Type
import Curry.Syntax.Utils ( field2Tuple )
import Env.Class ( ClassEnv, lookupClassInfo )
import Env.Determinism
import Env.Instance ( InstEnv )
import Env.TypeConstructor ( TCEnv, lookupTypeInfo, TypeInfo (..), rebindTypeInfo, qualLookupTypeInfo )
import Env.Value ( qualLookupValue, qualLookupValueUnique, ValueInfo(..), ValueEnv )
import Base.TopEnv (origName)

data DS = DS { detEnv :: TopDetEnv
             , localDetEnv :: NestDetEnv
             , valueEnv :: ValueEnv
             , classEnv :: ClassEnv
             , tcEnv :: TCEnv
             , moduleIdent :: ModuleIdent
             , freshIdent :: VarIndex
             , messages :: [Message]
             , signatures :: Map Ident DetExpr
             }

freshVar :: DM VarIndex
freshVar = do
  i <- gets freshIdent
  modify (\s -> s { freshIdent = i + 1 })
  return i

addLocalType :: IdentInfo -> DetScheme -> DM ()
addLocalType ii ty = do
  liftIO $ putStrLn $ "addLocalType: " ++ render (pPrint ii) ++ " " ++ render (pPrint ty)
  modify (\s -> s { localDetEnv = bindNestEnv ii ty (localDetEnv s) })

addExternalType :: IdentInfo -> DetScheme -> DM ()
addExternalType ii ty = do
  liftIO $ putStrLn $ "addExternalType: " ++ render (pPrint ii) ++ " " ++ render (pPrint ty)
  modify (\s -> s { detEnv = Map.insert ii ty (detEnv s) })

addMessage :: Message -> DM ()
addMessage msg = modify (\s -> s { messages = msg : messages s })

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

determinismCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> InstEnv -> DetEnv
                 -> Module PredType -> IO (DetEnv, TCEnv, [Message])
determinismCheck mid tce ve ce _ie de (Module _ _ _ _ _ _ ds') = flip evalStateT initState $ do
  uses <- getUseMap mid tce definingDS
  let groups = scc (declIdents mid tce)
                   (Set.toList . Set.unions . map (flip (Map.findWithDefault Set.empty) uses)
                                            . declIdents mid tce)
                   definingDS
  -- liftIO $ putStrLn $ render $ pPrint $ Map.toList uses
  -- liftIO $ putStrLn $ render $ pPrint $ map (map (declIdents mid tce)) groups
  mapM_ checkGroup groups
  env <- gets detEnv
  correctTCEnv ds'
  tce' <- gets tcEnv
  liftIO $ putStrLn $ prettyDetEnv env
  msgs <- gets messages
  return (env, tce', msgs)
  where
    sigs = foldr (Map.union . sigInf) Map.empty
    sigInf (DetSig _ is dty) = Map.fromList (map (,dty) is)
    sigInf (ClassDecl _ _ _ _ _ ds) = sigs ds
    sigInf _ = Map.empty
    initState = DS de (Top Map.empty) ve ce tce mid 0 [] (sigs ds')
    definingDS = filter isDefiningDecl ds'
    isDefiningDecl FunctionDecl {} = True
    isDefiningDecl PatternDecl {}  = True
    isDefiningDecl ClassDecl {}    = True
    isDefiningDecl InstanceDecl {} = True
    isDefiningDecl ExternalDecl {} = True
    isDefiningDecl _ = False

getUseMap :: ModuleIdent -> TCEnv -> [Decl PredType] -> DM (Map IdentInfo (Set IdentInfo))
getUseMap mid tce ds = do
  let go d = do
        is <- freeIdents d
        return (map (,is) (declIdents mid tce d))
  Map.unionsWith Set.union . map Map.fromList <$> mapM go ds

declIdents :: ModuleIdent -> TCEnv -> Decl PredType -> [IdentInfo]
declIdents mid _ (FunctionDecl _ _ f _) =
  [QI (qualifyWith mid f)]
declIdents mid _ (TypeSig _ ids _) =
  map (QI . qualifyWith mid) ids
declIdents mid _ (ExternalDecl _ ids) =
  map (\(Var _ i) -> QI $ qualifyWith mid i) ids
declIdents _   _   (PatternDecl _ pat _) =
  map (QI . qualify . fst3) (patternVars pat)
declIdents mid tcE (ClassDecl _ _ _ cls _ ds) =
  concatMap (map (toClassIdent (qualifyWith mid cls)) . declIdents mid tcE) ds
declIdents mid tcE (InstanceDecl _ _ _ cls ty _) = case qualLookupTypeInfo cls tcE of
  [TypeClass qcls _ meths] -> map (toInstanceIdent cls ty . QI
                                    . qualifyWith (fromMaybe mid (qidModule qcls))
                                    . methodName) meths
  _ -> internalError $ "DeterminismCheck.declIdents: "
          ++ show cls ++ " not found"
declIdents _ _ _ = []

toClassIdent :: QualIdent -> IdentInfo -> IdentInfo
toClassIdent cls (QI qid) = CI cls (zeroUniqueQual qid')
  where qid' = case qidModule qid of
            Nothing -> qualifyLike cls (unqualify qid)
            Just _  -> qid
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
  ListType sp _ -> toInstanceIdent cls (ConstructorType sp qListId) (QI qid)
  TupleType sp args -> toInstanceIdent cls (ConstructorType sp (qTupleId (length args))) (QI qid)
  ArrowType sp _ _ -> toInstanceIdent cls (ConstructorType sp qArrowId) (QI qid)
  ParenType _ ty' -> toInstanceIdent cls ty' (QI qid)
  ApplyType _ ty' _ -> toInstanceIdent cls ty' (QI qid)
  _ -> internalError (show ty ++ " is not a constructor type")
toInstanceIdent _ _ ii = ii

checkGroup :: [Decl PredType] -> DM ()
checkGroup ds = do
  mid <- gets moduleIdent
  tce <- gets tcEnv
  liftIO $ putStrLn $ render $ pPrint $ map (declIdents mid tce) ds
  constraints <- Set.unions <$> (mapM checkDecl ds >>= sequence)
  res <- Map.map abstractDetScheme . extractTopEnv <$> solveConstraints constraints
  liftIO $ putStrLn $ render $ pPrint $ Map.toList res
  -- By unioning with the old environment to the right, we make sure that
  -- we retain any signatures that were already present, such as user supplied ones.
  -- This ensures that we do not get follow up errors from incorrect function definitions.
  -- We take all user supplied signatures as ground truth.
  modify (\s -> s { localDetEnv = Top Map.empty, detEnv = Map.union (detEnv s) res,  freshIdent = 0 })
  checkSigs ds res
  return ()

checkSigs :: [Decl PredType] -> DetEnv -> DM ()
checkSigs ds' dE = do
  tcE <- gets tcEnv
  let getWhat d = case d of
        FunctionDecl {} -> "function definition"
        PatternDecl {}  -> "pattern definition"
        ClassDecl {}    -> "class method"
        InstanceDecl {} -> "instance method"
        _               -> "declaration"
      go mid _ what (ClassDecl _ _ _ cls _ ds) = mapM_ (go mid (toClassIdent (qualifyWith mid cls)) what) ds
      go mid _ what (InstanceDecl _ _ _ cls ty ds) = case qualLookupTypeInfo cls tcE of
        [inf] ->  mapM_ (go mid' (toInstanceIdent (origName inf) ty) what) ds
          where mid' = fromMaybe mid (qidModule (origName inf))
        _ -> internalError $ "DeterminismCheck.checkSigs: " ++ show cls ++ " not found"
      go mid to what d@FunctionDecl {} = do
        sigs <- gets signatures
        let sp = getSpanInfo d
            act (CI _ qid) dty1 = act (QI qid) dty1
            act (QI qid) dty1 = case Map.lookup i sigs of
              Nothing    -> return ()
              Just dty2' -> do
                  let dty2 = toDetType dty2'
                  d1 <- instantiate dty1
                  d2 <- instantiate dty2
                  case d1 `moreSpecific` d2 of
                    Just _  -> return ()
                    Nothing -> addMessage (errIncorrectSig sp i what dty1 dty2)
              where i = unqualify qid
            act (II cls _ qid) dty1 =
              case qualLookupTypeInfo cls tcE of
                [TypeClass _ _ mths] ->
                  let isCls (ClassMethod m _ _ _ _) = m == i
                  in case find isCls mths >>= methodDetSchemeAnn of
                      Just dty2 -> do
                        d1 <- instantiate dty1
                        d2 <- instantiate dty2
                        case d1 `moreSpecific` d2 of
                          Just _  -> return ()
                          Nothing -> addMessage (errIncorrectSig sp i what dty1 dty2)
                      Nothing -> return ()
                _ -> internalError $ "DeterminismCheck.checkSigs: " ++ show cls ++ " not found"
              where i = unqualify qid
        forM_ (declIdents mid tcE d) $ \i ->
          forM_ (Map.lookup (to i) dE) (act (to i))
      go _ _ _ _ = return ()
  mid <- gets moduleIdent
  mapM_ (\d -> go mid id (getWhat d) d) ds'

-- Registers the types of defined variables on the outer layer, creates constraints on the inner layer.
checkDecl :: Decl PredType -> DM (DM (Set DetConstraint))
checkDecl d@(FunctionDecl _ _ _ eqs) = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  checkFun (declIdents mid tcE d) eqs
checkDecl (PatternDecl _ p rhs) = do
  v <- freshVar
  (cs, _) <- checkPat v p
  return (Set.union cs <$> scoped (checkRhsTy v rhs))
checkDecl (ClassDecl _ _ _ cls _ ds) = do
  acts <- mapM (checkClassDecl cls) ds
  return (Set.unions <$> sequence acts)
checkDecl (InstanceDecl _ _ _ cls ty ds) = do
  acts <- mapM (checkInstanceDecl cls ty) ds
  tcE <- gets tcEnv
  mid <- gets moduleIdent
  case qualLookupTypeInfo cls tcE of
    [TypeClass qcls' _ mthds] -> do
      let qcls | isQualified qcls' = qcls'
               | otherwise         = qualifyWith mid (unqualify cls)
          getI (FunctionDecl _ _ i _) = Just (i { idUnique = 0 })
          getI _ = Nothing
          impl = mapMaybe getI ds
          unimpl = filter (\(ClassMethod i _ _ _ _) -> i `notElem` impl) mthds
      forM_ unimpl $ \(ClassMethod i _ (PredType _ ty') mbd _) -> case mbd of
        Just dty -> addLocalType (toInstanceIdent qcls ty (QI (qualifyLike qcls i))) dty
        Nothing  -> addLocalType (toInstanceIdent qcls ty (QI (qualifyLike qcls i))) (mkArrowLike ty')
      return (Set.unions <$> sequence acts)
    _ -> internalError $ "DeterminismCheck.checkDecl: " ++ show cls ++ " not found"
checkDecl (ExternalDecl _ vs) = do
  mid <- gets moduleIdent
  let go (Var (PredType _ ty) i) =
        let qi = qualifyWith mid i
        in case externalDetMap Map.!? qi of
              Nothing -> addLocalType (QI qi) (mkArrowLike ty)
              Just dty -> addLocalType (QI qi) dty
  mapM_ go vs
  return $ return Set.empty
checkDecl (FreeDecl _ vs) = do
  mapM_ (\(Var _ i) -> addLocalType (QI (qualify i)) (toDetSchema Nondet)) vs
  return $ return Set.empty
checkDecl _ = return $ return Set.empty

checkFun :: [IdentInfo] -> [Equation PredType] -> DM (DM (Set DetConstraint))
checkFun _ [] = internalError "DeterminismCheck.checkDecl: empty function"
checkFun is eqs@(e:_) = do
  let lhsArity OpLhs {} = 2
      lhsArity (FunLhs _ _ ps) = length ps
      lhsArity (ApLhs _ lhs ps) = lhsArity lhs + length ps
      arity = case e of Equation _ lhs _ -> lhsArity lhs
  ov <- overlaps eqs
  args <- replicateM arity freshVar
  res <- freshVar
  sigs <- gets signatures
  let varTyped = foldr (DetArrow . VarTy) (VarTy res) args
      getSig i = (i, Map.lookup (unqualify (identInfoFun i)) sigs)
      add (i, Just dty) = i `addExternalType` toDetType dty >>
                                  i `addLocalType` toDetSchema varTyped
      add (i, Nothing) = i `addLocalType` toDetSchema varTyped
      withSig = map getSig is
  -- Either add the signature type if it exists,
  -- or a type that is variable in each argument and the result.
  mapM_ add withSig
  return $ scoped $ do
    -- Equate the signature type with the variable stuff from above
    c1 <- Set.unions <$> mapM (\dty -> instantiate (toDetType dty)
                                  >>= getSignatureConstraints args res)
                              (mapMaybe snd withSig)
    let c2 = if ov then Set.singleton (EqualType res Nondet) else Set.empty
    Set.unions . ([c1, c2] ++) <$> mapM (checkEquation args res) eqs

getSignatureConstraints :: [VarIndex] -> VarIndex -> DetType -> DM (Set DetConstraint)
getSignatureConstraints (a:args) res (DetArrow d1 d2) = do
  c1 <- getSignatureConstraints args res d2
  return (Set.insert (EqualType a d1) c1)
getSignatureConstraints (a:args) res d = do
  -- When the user supplied type has less arguments than the function,
  -- the remaining arguments are equated with the result type of the user supplied type.
  c1 <- getSignatureConstraints args res d
  return (Set.insert (EqualType a d) c1)
getSignatureConstraints [] res d2 = return (Set.singleton (EqualType res d2))

checkEquation :: [VarIndex] -> VarIndex -> Equation PredType -> DM (Set DetConstraint)
checkEquation args res (Equation _ lhs rhs) = do
  (cs, is) <- checkLhs args lhs
  let demands = foldr (Set.insert . EqualType res . VarTy) Set.empty is -- for all demanded variables: res ~ alpha
  Set.union demands . Set.union cs <$> scoped (checkRhsTy res rhs)

-- Returns a set of constraints and a list of variables that are demanded strictly
checkLhs :: [VarIndex] -> Lhs PredType -> DM (Set DetConstraint, [VarIndex])
checkLhs vs (FunLhs _ _ ps) = do
  (css, stricts) <- unzip <$> zipWithM checkPat vs ps
  return (Set.unions css, map fst $ filter snd $ zip vs stricts)
checkLhs [v1, v2] (OpLhs _ p1 _ p2) = do
  (cs1, s1) <- checkPat v1 p1
  (cs2, s2) <- checkPat v2 p2
  return (Set.union cs1 cs2, map fst $ filter snd [(v1, s1), (v2, s2)])
checkLhs _ OpLhs {} = internalError "DeterminismCheck.genDetType: op with more than two arguments"
checkLhs vs (ApLhs _ lhs ps) = do
  let (vs1, vs2) = splitAt (length vs - length ps) vs
  (cs1, s1) <- checkLhs vs1 lhs
  (cs2, s2) <- unzip <$> zipWithM checkPat vs2 ps
  return (Set.union cs1 (Set.unions cs2), s1 ++ map fst (filter snd (zip vs2 s2)))

checkPat :: VarIndex -> Pattern PredType -> DM (Set DetConstraint, Bool)
checkPat v (VariablePattern _ _ i)
  | idName i == "_" = return (Set.empty, False)
  | otherwise = do
    addLocalType (QI (qualify i)) (toDetSchema (VarTy v))
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
  addLocalType (QI (qualify i)) (toDetSchema (VarTy v))
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
  -- return True, because we assume functional pattern to be demanded
  return (Set.insert c1 (Set.insert c2 (Set.union cs1 cs2)), True)
-- The next two need to be deterministic by design,
-- so we skip adding a dependency on numFreeIdent.
checkPat _ LiteralPattern {} = return (Set.empty, True)
checkPat _ NegativePattern {} = return (Set.empty, True)

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
checkExprTy v (Constructor _ (PredType _ ty) _) = do
  sc <- instantiate (mkArrowLike ty)
  return (Set.singleton (EqualType v sc))
checkExprTy v (Tuple _ es) =
  Set.unions <$> mapM (checkExprTy v) es
checkExprTy v (List _ _ es) =
  Set.unions <$> mapM (checkExprTy v) es
checkExprTy v (ListCompr _ e qs) =
  checkStmts v e qs
checkExprTy v ee@(EnumFrom _ e) = do
  let ety = typeOf e
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety eety)
  Set.union
    <$> checkVar v enumTy qEnumFromId
    <*> checkExprTy v e
checkExprTy v ee@(EnumFromThen _ e1 e2) = do
  let ety = typeOf e1
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety (TypeArrow ety eety))
  Set.unions <$> sequence
    [ checkVar v enumTy qEnumFromThenId
    , checkExprTy v e1
    , checkExprTy v e2 ]
checkExprTy v ee@(EnumFromTo _ e1 e2) = do
  let ety = typeOf e1
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety (TypeArrow ety eety))
  Set.unions <$> sequence
    [ checkVar v enumTy qEnumFromToId
    , checkExprTy v e1
    , checkExprTy v e2 ]
checkExprTy v ee@(EnumFromThenTo _ e1 e2 e3) = do
  let ety = typeOf e1
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety (TypeArrow ety (TypeArrow ety eety)))
  Set.unions <$> sequence
    [ checkVar v enumTy qEnumFromThenToId
    , checkExprTy v e1
    , checkExprTy v e2
    , checkExprTy v e3 ]
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
      cs' = foldr ((Set.insert . EqualType v' . VarTy) . fst)
              (Set.insert c (Set.unions cs))
              (filter snd $ zip vs stricts)
  Set.union cs' <$> checkExprTy v' e
checkExprTy v (Let _ _ ds e) = scoped $ do
  cs <- checkLocalDeclsTy ds
  Set.union cs <$> checkExprTy v e
checkExprTy v (Do _ _ ss e) = do
  tcE <- gets tcEnv
  let (ety, inner) = case typeOf e of
        ety'@(TypeApply _ inner') -> (ety', inner')
        _ -> internalError "DeterminismCheck.checkExprTy: do expression not of type constructor"
      bindTy = PredType emptyPredSet (TypeArrow ety (TypeArrow
        (TypeArrow inner ety)
        ety))
      failTy = PredType emptyPredSet (TypeArrow
        (TypeApply (TypeConstructor qListId) (TypeConstructor qCharId))
        ety)
  Set.unions <$> sequence
    ( [ checkStmts v e ss
      , checkVar v bindTy qBindId ]
    ++
      [ checkVar v failTy qFailId | any (stmtCanFail tcE) ss]
    )
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
checkExprTy v (IfThenElse _ e1 e2 e3) =
  Set.unions <$> mapM (checkExprTy v) [e1, e2, e3]
checkExprTy v (Case _ _ _ e bs) = do
  cs <- checkExprTy v e
  Set.unions . (cs:) <$> mapM (scoped . checkAlt v) bs
-- Once again, next two are to be deterministic by design,
-- since their pattern variants are needed to be deterministic.
-- Thus we skip adding a dependency on numFreeIdent.
checkExprTy v (UnaryMinus _ e) = checkExprTy v e
checkExprTy v Literal {} = return (Set.singleton (EqualType v Det))

checkAlt :: VarIndex -> Alt PredType -> DM (Set DetConstraint)
checkAlt v (Alt _ p rhs) = do
  cs <- fst <$> checkPat v p
  Set.union cs <$> checkRhsTy v rhs

checkStmts :: VarIndex -> Expression PredType -> [Statement PredType] -> DM (Set DetConstraint)
checkStmts v e [] = checkExprTy v e
checkStmts v e (s:ss) = case s of
  StmtDecl _ _ ds ->
    scoped $ Set.union <$> checkLocalDeclsTy ds <*> checkStmts v e ss
  StmtExpr _ e2   ->
    Set.union <$> checkExprTy v e2 <*> checkStmts v e ss
  StmtBind _ p e2 ->
    Set.union
      <$> checkExprTy v e2
      <*> scoped (Set.union <$> fmap fst (checkPat v p) <*> checkStmts v e ss)

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
    Nothing -> Set.singleton . EqualType v <$> instantiate (mkArrowLike ty)
    Just ii -> do
      lcl <- gets localDetEnv
      ext <- gets detEnv
      case Map.lookup ii ext of
        Just ty'
          | detCtx -> Set.singleton . EqualType v <$> instantiate ty'
          | otherwise -> return $ Set.singleton $ EqualType v Nondet
        Nothing -> case lookupNestEnv ii lcl of
          Just ty'
            | detCtx    -> Set.singleton . EqualType v <$> instantiate ty'
            | otherwise -> return $ Set.singleton $ EqualType v Nondet
          Nothing -> internalError $ "checkVar: " ++ prettyII ii ++ " not found in "
                                        ++ prettyDetEnv (Map.union ext (flattenNestEnv lcl))
                                        ++ ". Original types:" ++ render (pPrint (ty, preds))

andM :: (Foldable t, Monad m) => (a -> m Bool) -> t a -> m Bool
andM f = foldr (\a b -> f a >>= \a' -> if a' then b else return False) (return True)

checkPred :: Pred -> DM Bool
checkPred (Pred cls ty) = do
  mid <- gets moduleIdent
  clsEnv <- gets classEnv
  lcl <- gets localDetEnv
  ext <- gets detEnv
  let qcls = qualQualify mid cls
  case lookupClassInfo qcls clsEnv of
    Nothing -> internalError $ "checkPred: " ++ render (pPrint cls) ++ " not found"
    Just (_, meths) -> flip andM meths $ \(m, _, _) ->
      case unapplyType True ty of
        (TypeConstructor tc, _) ->
          let qtc | isQualified tc = tc
                  | otherwise      = qualifyWith mid (unqualify tc)
              ii = II qcls qtc (zeroUniqueQual (qualifyLike qcls m))
          in case lookupNestEnv ii lcl of
            Just sc -> return (notNondet sc)
            Nothing -> case Map.lookup ii ext of
              Just sc -> return (notNondet sc)
              Nothing -> internalError $ "checkPred: " ++ prettyII ii ++ " not found in "
                            ++ prettyDetEnv (Map.union ext (flattenNestEnv lcl))
        _ -> return True

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

checkLocalDeclsTy :: [Decl PredType] -> DM (Set DetConstraint)
checkLocalDeclsTy ds = Set.unions <$> (mapM checkLocalDecl ds >>= sequence)
  where
    -- Like checkDecl, but does not qualify identifiers with the module identifier.
    checkLocalDecl :: Decl PredType -> DM (DM (Set DetConstraint))
    checkLocalDecl (PatternDecl _ p rhs) = do
      v <- freshVar
      (cs, _) <- checkPat v p
      return (Set.union cs <$> scoped (checkRhsTy v rhs))
    checkLocalDecl d@(FunctionDecl _ _ _ eqs) = do
      mid <- gets moduleIdent
      tcE <- gets tcEnv
      let unqualII (QI i) = QI $ qualify $ unqualify i
          unqualII (CI cls i) = CI cls $ qualify $ unqualify i
          unqualII (II cls tc i) = II cls tc $ qualify $ unqualify i
          is = map unqualII (declIdents mid tcE d)
      checkFun is eqs
    checkLocalDecl (ExternalDecl _ vs) = do
      let go (Var (PredType _ ty) i) =
            let qi = qualify i
            in case externalDetMap Map.!? qi of
                  Nothing -> addLocalType (QI qi) (mkArrowLike ty)
                  Just dty -> addLocalType (QI qi) dty
      mapM_ go vs
      return $ return Set.empty
    checkLocalDecl (FreeDecl _ vs) = do
      mapM_ (\(Var _ i) -> addLocalType (QI (qualify i)) (toDetSchema Nondet)) vs
      return $ return Set.empty
    checkLocalDecl _ = return $ return Set.empty

checkClassDecl :: Ident -> Decl PredType -> DM (DM (Set DetConstraint))
checkClassDecl cls d@(FunctionDecl _ _ _ eqs) = do
  mid <- gets moduleIdent
  clsEnv <- gets classEnv
  tcE <- gets tcEnv
  case lookupClassInfo (qualifyWith mid cls) clsEnv of
    Nothing -> internalError $ "checkClassDecl: " ++ show cls ++ " not found"
    Just (_, _) -> do
        -- Add class method `d` on global scope (happens in outer layer of checkFun)
        let is = map (toClassIdent (qualifyWith mid cls)) (declIdents mid tcE d)
        act <- checkFun is eqs
        return $ scoped act
checkClassDecl _ _ = return $ return Set.empty

checkInstanceDecl :: QualIdent -> InstanceType -> Decl PredType -> DM (DM (Set DetConstraint))
checkInstanceDecl cls ty d@(FunctionDecl _ _ _ eqs) = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  case qualLookupTypeInfo cls tcE of
    [TypeClass qcls _ cm] -> do
      let mid' = fromMaybe mid (qidModule qcls)
          is = map (toInstanceIdent (qualQualify mid' cls) ty) (declIdents mid' tcE d)
          addSig m@(ClassMethod qid _ _ _ _) = case methodDetSchemeAnn m of
            Nothing  -> return ()
            Just dty -> do
              modify (\s -> s { signatures = Map.insert qid (toDetExpr dty) (signatures s) } )
      mapM_ addSig cm
      act <- checkFun is eqs
      return $ scoped act
    _ -> internalError $ "checkInstanceDecl: " ++ show cls ++ " not found"
checkInstanceDecl _ _ _ = return $ return Set.empty

solveConstraints :: Set DetConstraint -> DM NestDetEnv
solveConstraints constraints = do
  liftIO $ putStrLn $ render $ pPrint $ Set.toList constraints
  let grps = scc defs uses $ Set.toAscList constraints
  liftIO $ putStrLn $ render $ pPrint $ grps
  solved <- foldM solveGroup Map.empty grps
  lcl <- gets localDetEnv
  return $ mapNestEnv (`substDetSchema` solved) lcl
  where
    -- TODO: useless to group this
    defs (AppliedType v w _) = [v, w]
    defs (EqualType v ty) = v : detTypeVars ty
    uses (AppliedType v w ty) = v : w : concatMap detTypeVars ty
    uses (EqualType v ty) = v : detTypeVars ty

-- TODO not monadic
solveGroup :: Map VarIndex DetType -> [DetConstraint] -> DM (Map VarIndex DetType)
solveGroup solutions = go Map.empty . map (`substCon` solutions)
  where
    go current [] = return $ Map.union current solutions
    go current (c:cs) = do
      liftIO $ putStrLn $ render $ pPrint $ Map.toList current
      liftIO $ putStrLn $ render $ pPrint c
      case c of
        AppliedType v w tys ->
          case Map.lookup w current of
            -- Applied types are always the last entries in the list,
            -- so w can only be constrained by an applied type.
            Nothing -> go current cs
            Just ty -> case Map.lookup v current of
              Nothing -> go (Map.insert v (applyTy ty tys) current) cs
              Just ty' -> case unify ty' (applyTy ty tys) current cs of
                (new, cs') -> go (Map.insert v new current)  cs' -- TODO: Might fail if v has been equated to Det already and application is Nondet
        EqualType v ty
          | ty == VarTy v -> go current cs
          | v `elem` detTypeVars ty -> go (Map.insert v Nondet current) cs
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
    unify (DetArrow ty1 ty2) Det current cs =
      let (new1, cs1) = unify ty1 Det current cs
          (new2, cs2) = unify ty2 Det current cs1
      in (DetArrow new1 new2, cs2)
    unify Det (DetArrow ty1 ty2) current cs =
      let (new1, cs1) = unify Det ty1 current cs
          (new2, cs2) = unify Det ty2 current cs1
      in (DetArrow new1 new2, cs2)

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

lessSpecific :: DetType -> DetType -> Maybe (Map VarIndex DetType)
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

-- The TC environment must be updated to add determinism information
-- to the (user-supplied or generated) default implementation of a class method
correctTCEnv :: [Decl PredType] -> DM ()
correctTCEnv ds' = do
  res <- concatMapM collect ds'
  mapM_ enter res
  where
    collect (ClassDecl _ _ _ cls _ ds) = do
      let allIds = concatMap sigIdents ds
          funIds = concatMap funIdents ds
      res <- (++) <$> mapM (correctClassDecl cls) funIds
                  <*> mapM (correctClassSig cls) (allIds \\ funIds)
      return [(cls, res)]
    collect _ = return []
    sigIdents (TypeSig _ is _) = is
    sigIdents _ = []
    funIdents (FunctionDecl _ _ i _) = [i]
    funIdents _ = []
    correctClassDecl cls i = do
      mid <- gets moduleIdent
      dEnv <- gets detEnv
      let i0 = i { idUnique = 0 }
      case Map.lookup (CI (qualifyWith mid cls) (qualifyWith mid i0)) dEnv of
        Nothing  -> internalError $ "correctTCEnv: " ++ show (cls, i) ++ " not found"
        Just dty -> return (i0, dty)
    correctClassSig _ i = return (i { idUnique = 0 }, Forall [] Det)
    enter (cls, newInfo) = do
      m <- gets moduleIdent
      tce <- gets tcEnv
      case lookupTypeInfo cls tce of
        [TypeClass cls' k ms] ->
          let ms' = map update ms
              update (ClassMethod i a ty _ mdty) = case lookup i newInfo of
                Nothing -> internalError $ "correctTCEnv.enter.update: "
                              ++ show (cls, i) ++ " not found in" ++ show newInfo
                Just dty -> ClassMethod i a ty (Just dty) mdty
          in modify $ \s -> s { tcEnv = rebindTypeInfo m cls (TypeClass cls' k ms') tce }
        _ -> internalError $ "correctTCEnv.enter: " ++ show cls ++ " not found"

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
  freeIdents (Equation _ lhs e) = freeIdents lhs `unionM` freeIdents e

instance DetCheck (Lhs PredType) where
  freeIdents (FunLhs _ _ ps) = freeIdents ps
  freeIdents (OpLhs _ p1 _ p2) = freeIdents p1 `unionM` freeIdents p2
  freeIdents (ApLhs _ lhs ps) = freeIdents lhs `unionM` freeIdents ps

instance DetCheck (Pattern PredType) where
  freeIdents (VariablePattern {}) = return Set.empty
  freeIdents (ConstructorPattern _ _ _ ps) = freeIdents ps
  freeIdents (InfixPattern _ _ p1 _ p2) = freeIdents p1 `unionM` freeIdents p2
  freeIdents (ParenPattern _ p) = freeIdents p
  freeIdents (RecordPattern _ _ _ fs) = freeIdents fs
  freeIdents (TuplePattern _ ps) = freeIdents ps
  freeIdents (ListPattern _ _ ps) = freeIdents ps
  freeIdents (AsPattern _ _ p) = freeIdents p
  freeIdents (LazyPattern _ p) = freeIdents p
  freeIdents (FunctionPattern _ (PredType _ ty) i ps) = do
    mii <- variableFreeIdent i ty
    case mii of
      Nothing -> return Set.empty
      Just ii -> Set.insert ii <$> freeIdents ps
  freeIdents (InfixFuncPattern _ (PredType _ ty) p1 i p2) = do
    mii <- variableFreeIdent i ty
    case mii of
      Nothing -> return Set.empty
      Just ii -> Set.insert ii <$> freeIdents [p1, p2]
  -- Yet again, the next two need to be deterministic by design,
  -- so we skip adding a dependency on numFreeIdent.
  freeIdents LiteralPattern {} = return Set.empty
  freeIdents NegativePattern {} = return Set.empty

instance DetCheck (Expression PredType) where
  freeIdents (Variable _ (PredType _ ty) i) =
    maybe Set.empty Set.singleton <$> variableFreeIdent i ty
  freeIdents (Typed _ e _) = freeIdents e
  freeIdents (Apply _ e1 e2) = freeIdents e1 `unionM` freeIdents e2
  freeIdents (InfixApply _ e1 op e2) =
    freeIdents e1 `unionM` freeIdents e2 `unionM` freeIdents op
  freeIdents (Lambda _ _ e) = freeIdents e
  freeIdents (Let _ _ ds e) = freeIdents ds `unionM` freeIdents e
  freeIdents edo@(Do _ _ ss e) = do
    tcE <- gets tcEnv
    freeIdents ss `unionM` freeIdents e `unionM`
      monadFreeIdent (typeOf edo) `unionM`
      if any (stmtCanFail tcE) ss then monadFailFreeIdent (typeOf edo) else return Set.empty
  freeIdents (List _ _ es) = freeIdents es
  freeIdents Constructor {} = return Set.empty
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
  freeIdents (IfThenElse _ e1 e2 e3) =
    freeIdents e1 `unionM` freeIdents e2 `unionM` freeIdents e3
  freeIdents (Case _ _ _ e bs) = freeIdents e `unionM` freeIdents bs
  -- Once again, next two are to be deterministic by design,
  -- since their pattern variants are needed to be deterministic.
  -- Thus we skip adding a dependency on numFreeIdent.
  freeIdents (UnaryMinus _ e) = freeIdents e
  freeIdents Literal {} = return Set.empty

instance DetCheck (InfixOp PredType) where
  freeIdents (InfixOp (PredType _ ty) i) =
    maybe Set.empty Set.singleton <$> variableFreeIdent i ty
  freeIdents (InfixConstr _ _) =
    return Set.empty

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
    _ -> return Set.empty

monadFreeIdent :: Type -> DM (Set IdentInfo)
monadFreeIdent ty =
  case unapplyType True ty of
    (TypeConstructor tc, _) ->
      return (Set.singleton (II qMonadId tc qBindId))
    _ -> return Set.empty

monadFailFreeIdent :: Type -> DM (Set IdentInfo)
monadFailFreeIdent ty =
  case unapplyType True ty of
    (TypeConstructor tc, _) ->
      return (Set.singleton (II qMonadFailId tc qFailId))
    _ -> return Set.empty

variableFreeIdent :: QualIdent -> Type -> DM (Maybe IdentInfo)
variableFreeIdent qid ty = do
  vEnv <- gets valueEnv
  mid <- gets moduleIdent
  case qualLookupValueUnique mid qid vEnv of
    [Value orig mci _ (ForAll _ (PredType _ ty'))] -> case mci of
      Nothing -> return (Just (QI (zeroUniqueQual orig)))
      Just cls ->
        let qcls = qualifyLike orig (unqualify cls)
            sub = matchType ty' ty idSubst
            -- 0 = class type variable
            clsTy = subst sub (TypeVariable 0)
        in case unapplyType True clsTy of
            (TypeConstructor tc, _)
              -> return (Just (II qcls tc (zeroUniqueQual (qualQualify mid orig))))
            _ -> return Nothing
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
prettyII = render . pPrint

prettyScheme :: DetScheme -> String
prettyScheme = render . pPrint

stmtCanFail :: TCEnv -> Statement PredType -> Bool
stmtCanFail tcE (StmtBind _ p _) = checkFailablePattern tcE p
stmtCanFail _ _ = False

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

errIncorrectSig :: SpanInfo -> Ident -> String -> DetScheme -> DetScheme -> Message
errIncorrectSig p i what (Forall _ dty1) (Forall _ dty2) = spanInfoMessage p $ vcat
  [ text "Incorrect determinism signature for" <+> text what <> colon <+> pPrint i
  , text "Inferred signature:" <+> pPrint dty1
  , text "Given signature:" <+> pPrint dty2
  , text "The inferred signature is more restrictive than the given signature."
  ]
