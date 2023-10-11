{- |
    Module      :  $Header$
    Description :  Determinism checking of Curry programs
    Copyright   :  (c) 2023 - 2023 Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    After the compiler has type checked the program,
    it also infers the determinism types of all functions
    and checks if their determinism signatures are correct.

    It is crucial that we have the full type information available.
    This check uses all previously populated environments
    and adds the inferred types to the determinism compiler environment.
    Note that we also update the type constructor environment with the information
    about the determinism types of type class determinism signatures and
    the determinism type of its default method implementations constructors.

    The determinism check works as follows:
      - First we collect the define/use relationships of all declarations.
        Note that this is more granular than the one used for previous compiler phases,
        because we distinguish even between different type class instances.
      - Then we split all declarations into strongly connected components (SCCs)
        for the same reason as in previous checks.
      - Next, we check each SCC in isolation.
        In each one, we first add all information about the determinism signatures,
        Going further, we traverse the syntax tree and collect constraints on the determinism types.
        We use a nested environment to keep track of the local variables.
        The constraints are then solved using a modified unification algorithm.
        The algorithm is modified to handle the special kind of subtyping relation of
        determinism types.
        The result of the unification is a substitution that is applied to the constraints.
        Finally, we check the determinism signatures of each declaration in the SCC
        against the inferred types.
      - Since previous checks left the determinism information in the type constructor env for
        type classes empty, we now fix this by entering that information into the environment.

    The determinism check returns the updated determinism and type constructor environments,
    the declarations annotated with both the type and the determinism type,
    as well as a list of messages that were generated during the check
    Only when the list of messages is empty, the check was successful.
-}
{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
module Checks.DeterminismCheck (determinismCheck, applyDetType) where

import Prelude hiding ( (<>) )
import Control.Arrow ( second )
import Control.Monad ( liftM2, void, zipWithM, replicateM, forM_, forM, unless, mapAndUnzipM, foldM )
import Control.Monad.Extra ( concatMapM )
import Control.Monad.State ( evalState, modify, gets, State )
import Data.Equivalence.Monad ( runEquivM, EquivM, MonadEquiv(..) )
import Data.List ( nub, (\\), find, sortOn )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( fromMaybe, mapMaybe, catMaybes )
import Data.Set ( Set )
import qualified Data.Set as Set

import Base.Messages ( Message, internalError, spanInfoMessage )
import Base.SCC ( scc )
import Base.TopEnv (origName)
import Base.TypeExpansion (expandType)
import Base.Types
import Base.TypeSubst ( idSubst, subst )
import Base.Typing ( patternVars, typeOf, matchType )
import Base.Utils ( fst3, fth4, fst4 )
import Checks.TypeCheck ( checkFailablePattern )
import Curry.Base.Ident
import Curry.Base.Pretty ( Pretty(..), render, vcat, text, (<+>), (<>), colon, hsep )
import Curry.Base.SpanInfo ( SpanInfo(..), HasSpanInfo (..) )
import Curry.Syntax.Type
import Curry.Syntax.Utils ( field2Tuple )
import Env.Class ( ClassEnv, lookupClassInfo )
import Env.Determinism
import Env.Instance ( InstEnv, lookupInstInfo )
import Env.TypeConstructor ( TCEnv, lookupTypeInfo, TypeInfo (..), rebindTypeInfo, qualLookupTypeInfo )
import Env.Value ( qualLookupValue, qualLookupValueUnique, ValueInfo(..), ValueEnv )

determinismCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> InstEnv -> DetEnv
                 -> [KnownExtension] -> Module PredType
                 -> (DetEnv, TCEnv, [Decl (PredType, DetType)], [Message])
determinismCheck mid tce ve ce ie de exts (Module _ _ _ _ _ _ ds) = flip evalState initState $ do
  uses <- getUseMap mid tce ds
  let groups = scc (declIdents ie mid tce . fst)
                   (Set.toList . Set.unions . map (flip (Map.findWithDefault Set.empty) uses)
                                            . declIdents ie mid tce . fst)
                   (zip ds [1..])
  ds' <- concat <$> mapM checkGroup groups
  env <- gets detEnv
  correctTCEnv ds
  tce' <- gets tcEnv
  msgs <- gets messages
  return (env, tce', map fst $ sortOn snd ds', msgs)
  where
    extSet = Set.fromList exts
    sigMap = sigs ds
    sigs = foldr (Map.union . sigInf) Map.empty
    sigInf (DetSig _ is dty) = Map.fromList (map (,dty) is)
    sigInf (ClassDecl _ _ _ _ _ ds') = sigs ds'
    sigInf _ = Map.empty
    initState = DS de (Top Map.empty) ve ce tce ie mid 0 [] sigMap extSet

data DS = DS { detEnv :: TopDetEnv
             , localDetEnv :: NestDetEnv
             , valueEnv :: ValueEnv
             , classEnv :: ClassEnv
             , tcEnv :: TCEnv
             , instEnv :: InstEnv
             , moduleIdent :: ModuleIdent
             , freshIdent :: VarIndex
             , messages :: [Message]
             , signatures :: Map Ident DetExpr
             , extensions :: Set KnownExtension
             }

type DM = State DS

freshVar :: DM VarIndex
freshVar = do
  i <- gets freshIdent
  modify (\s -> s { freshIdent = i + 1 })
  return i

addLocalType :: IdentInfo -> DetScheme -> DM ()
addLocalType ii ty =
  modify (\s -> s { localDetEnv = bindNestDetEnv ii ty (localDetEnv s) })

addExternalType :: IdentInfo -> DetScheme -> DM ()
addExternalType ii ty =
  modify (\s -> s { detEnv = Map.insert ii ty (detEnv s) })

addMessage :: Message -> DM ()
addMessage msg = modify (\s -> s { messages = msg : messages s })

enterScope :: DM ()
enterScope = modify (\s -> s { localDetEnv = nestDetEnv (localDetEnv s) })

exitScope :: DM ()
exitScope = modify (\s -> s { localDetEnv = unnestDetEnv (localDetEnv s) })

scoped :: DM a -> DM a
scoped act = do
  enterScope
  res <- act
  exitScope
  return res

getUseMap :: ModuleIdent -> TCEnv -> [Decl PredType] -> DM (Map IdentInfo (Set IdentInfo))
getUseMap mid tce ds = do
  iE <- gets instEnv
  let go d = do
        is <- freeIdents d
        return (map (,is) (declIdents iE mid tce d))
  Map.unionsWith Set.union . map Map.fromList <$> mapM go ds

declIdents :: InstEnv -> ModuleIdent -> TCEnv -> Decl PredType -> [IdentInfo]
declIdents _  mid _ (FunctionDecl _ _ f _) =
  [QI (qualifyWith mid f)]
declIdents _  mid _ (TypeSig _ ids _) =
  map (QI . qualifyWith mid) ids
declIdents _  mid _ (ExternalDecl _ ids) =
  map (\(Var _ i) -> QI $ qualifyWith mid i) ids
declIdents _  _   _   (PatternDecl _ pat _) =
  map (QI . qualify . fst3) (patternVars pat)
declIdents iE mid tcE (ClassDecl _ _ _ cls _ ds) =
  concatMap (map (toClassIdent (qualifyWith mid cls)) . declIdents iE mid tcE) ds
declIdents _  mid tcE (InstanceDecl _ _ _ cls ty _) =
  instIdent mid tcE ty cls
declIdents ie mid tcE (DataDecl _ tc args cs deriv) =
  dataIdents ie mid tcE tc args (concatMap conFields cs) deriv
declIdents ie mid tcE (NewtypeDecl _ tc args c deriv) =
  dataIdents ie mid tcE tc args (conFields c) deriv
declIdents _  _ _ (FreeDecl _ vs) =
  map (\(Var _ i) -> QI $ qualify i) vs
declIdents _  _ _ _ = []

dataIdents :: InstEnv -> ModuleIdent -> TCEnv -> Ident -> [Ident] -> [Ident] -> [QualIdent] -> [IdentInfo]
dataIdents iE mid tcE tc args fields clss =
  map (QI . qualifyWith mid) fields ++
  concatMap (instIdent mid tcE ty)
    case lookupInstInfo (qDataId, qualifyWith mid tc) iE of
      Just _ -> qDataId : clss
      _      -> clss
  where
    ty = foldl (\a -> ApplyType NoSpanInfo a . VariableType NoSpanInfo)
           (ConstructorType NoSpanInfo (qualifyWith mid tc)) args

instIdent :: ModuleIdent -> TCEnv -> InstanceType -> QualIdent -> [IdentInfo]
instIdent mid tcE ty cls = case qualLookupTypeInfo cls tcE of
  [TypeClass qcls _ meths] -> map (toInstanceIdent mid tcE cls ty . QI
                                    . qualifyWith (fromMaybe mid (qidModule qcls))
                                    . methodName) meths
  _ -> internalError $ "DeterminismCheck.declIdents: "
          ++ show cls ++ " not found"

-- -----------------------------------------------------------------------------
-- * Checking declaration groups and traversing the AST to generate constraints
-- -----------------------------------------------------------------------------

checkGroup :: [(Decl PredType, Integer)] -> DM [(Decl (PredType, DetType), Integer)]
checkGroup ds = do
  let checkD (d, i) = fmap (second (,i)) <$> checkDecl d
  (constraintsList, ds') <- unzip <$> (mapM checkD ds >>= sequence)
  let constraints = Set.unions constraintsList
  lcl <- gets localDetEnv
  solved <- solveConstraints constraints
  let res = Map.map abstractDetScheme $ extractTopDetEnv $ mapNestDetEnv (`substDetSchema` solved) lcl
  -- By unioning with the old environment to the right, we make sure that
  -- we retain any signatures that were already present, such as user supplied ones.
  -- This ensures that we do not get follow up errors from incorrect function definitions.
  -- We take all user supplied signatures as ground truth.
  modify (\s -> s { localDetEnv = Top Map.empty
                  , detEnv = Map.union (detEnv s) res
                  , freshIdent = 0 })
  checkSigs (map fst ds) res
  -- Fix the annotations by looking up any determinism types from the full environment
  -- and instantiating that type with fresh variables.
  -- We also need the substitution from the constraint solving step to apply
  -- it to any determinism types annotated at any expressions that are not found in the
  -- environment (e.g. the annotation on lists or local functions).
  mapM (\(d, i) -> (,i) <$> fixDecl solved d) ds'

data DetConstraint = EqualType VarIndex DetType -- v ~ alpha
                   | AppliedType VarIndex VarIndex [DetType] -- v ~ y @ alpha1 ... alphan
  deriving (Eq, Ord, Show)

instance Pretty DetConstraint where
  pPrint (EqualType v ty) =
    pPrint (VarTy v) <+> text "~" <+> pPrint ty
  pPrint (AppliedType v y tys) =
    pPrint (VarTy v) <+> text "~" <+> pPrint (VarTy y) <+>
    text "@" <+> hsep (map pPrint tys)

checkSigs :: [Decl PredType] -> DetEnv -> DM ()
checkSigs ds' dE = do
  tcE <- gets tcEnv
  exts <- gets extensions
  iE <- gets instEnv
  let getWhat d = case d of
        FunctionDecl {} -> "function definition"
        PatternDecl {}  -> "pattern definition"
        ClassDecl {}    -> "class method"
        InstanceDecl {} -> "instance method"
        _               -> "declaration"
      go mid _ what (ClassDecl _ _ _ cls _ ds) = mapM_ (go mid (toClassIdent (qualifyWith mid cls)) what) ds
      go mid _ what (InstanceDecl _ _ _ cls ty ds) = case qualLookupTypeInfo cls tcE of
        [inf] ->  mapM_ (go mid' (toInstanceIdent mid tcE (origName inf) ty) what) ds
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
                  case d2 `lessSpecific` d1 of
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
                        case d2 `lessSpecific` d1 of
                          Just _  -> return ()
                          Nothing -> addMessage (errIncorrectSig sp i what dty1 dty2)
                      Nothing -> return ()
                _ -> internalError $ "DeterminismCheck.checkSigs: " ++ show cls ++ " not found"
              where i = unqualify qid
        forM_ (declIdents iE mid tcE d) $ \i ->
          forM_ (Map.lookup (to i) dE) (act (to i))
      go _ _ _ (DetSig sp _ _) =
        unless (DeterminismSignatures `Set.notMember` exts) $
          addMessage $ errDeterminismSignatureExt sp
      go _ _ _ _ = return ()
  mid <- gets moduleIdent
  mapM_ (\d -> go mid id (getWhat d) d) ds'

-- Registers the types of defined variables on the outer layer, creates constraints on the inner layer.
checkDecl :: Decl PredType -> DM (DM (Set DetConstraint, Decl (PredType, DetType)))
checkDecl d@(FunctionDecl spi pty f eqs) = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  iE <- gets instEnv
  act <- checkFun (declIdents iE mid tcE d) eqs
  return $ do
    (cs, dty, eqs') <- act
    return (cs, FunctionDecl spi (pty, dty) f eqs')
checkDecl (PatternDecl spi p rhs) = do
  v <- freshVar
  (cs1, _, p') <- checkPat v p
  (cs2, rhs') <- scoped (checkRhsTy v rhs)
  return $ return (Set.union cs1 cs2, PatternDecl spi p' rhs')
checkDecl (ClassDecl spi li ctx cls v ds) = do
  acts <- mapM (checkClassDecl cls) ds
  return $ do
    (css, ds') <- unzip <$> sequence acts
    return (Set.unions css, ClassDecl spi li ctx cls v ds')
checkDecl (InstanceDecl spi li ctx cls ty ds) = do
  acts <- mapM (checkInstanceDecl cls ty) ds
  tcE <- gets tcEnv
  cE <- gets classEnv
  mid <- gets moduleIdent
  case qualLookupTypeInfo cls tcE of
    [TypeClass qcls' _ _] -> do
      let qcls = case qualLookupTypeInfo qcls' tcE of
                   [TypeClass qcls'' _ _] -> qcls''
                   _ -> internalError $ "DeterminismCheck.checkDecl: " ++ show qcls' ++ " not found"
          getI (FunctionDecl _ _ i _) = Just (i { idUnique = 0 })
          getI _ = Nothing
          impl = mapMaybe getI ds
          unimpl = case lookupClassInfo qcls cE of
            Just (_, mthds) -> filter (\(i,_,_,_) -> i `notElem` impl) mthds
            _ -> internalError $ "DeterminismCheck.checkDecl: " ++ show qcls ++ " not found"
      forM_ unimpl $ \(i, _, _, mbd) -> case mbd of
        Just dty -> addLocalType (toInstanceIdent mid tcE qcls ty (QI (qualifyLike qcls i))) dty
        Nothing  -> addLocalType (toInstanceIdent mid tcE qcls ty (QI (qualifyLike qcls i))) (Forall [] Any)
      return $ do
        (css, ds') <- unzip <$> sequence acts
        return (Set.unions css, InstanceDecl spi li ctx cls ty ds')
    _ -> internalError $ "DeterminismCheck.checkDecl: " ++ show cls ++ " not found"
checkDecl (ExternalDecl spi vs) = do
  mid <- gets moduleIdent
  sigs <- gets signatures
  let go (Var pty@(PredType _ ty) i) = do
        dty <- case Map.lookup i sigs of
          Just de -> do
            let dty = toDetType de
            addExternalType (QI $ qualifyWith mid i) dty
            return dty
          Nothing  -> return (mkArrowLike ty)
        addLocalType (QI $ qualifyWith mid i) dty
        dtyi <- instantiate dty
        return (Var (pty, dtyi) i)
  vs' <- mapM go vs
  return $ return (Set.empty, ExternalDecl spi vs')
checkDecl (FreeDecl spi vs) = do
  vs' <- forM vs $ \(Var pty i) -> do
    addLocalType (QI (qualify i)) (toDetSchema Any)
    return (Var (pty, Any) i)
  return $ return (Set.empty, FreeDecl spi vs')
checkDecl (DataDecl spi tc vs constrs deriv) = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  let recType = Forall [0] (DetArrow (VarTy 0) (VarTy 0))
      tys = map (fromType [] . expandType mid tcE . toType []) $ concatMap conTypes constrs
  mapM_ (\f -> addLocalType (QI $ qualifyWith mid f) recType) $ concatMap conFields constrs
  act <- checkDerive tc tys deriv
  return $ do
    cs <- act
    return (cs, DataDecl spi tc vs constrs deriv)
checkDecl (NewtypeDecl spi tc vs constr deriv) = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  let recType = Forall [0] (DetArrow (VarTy 0) (VarTy 0))
      tys = map (fromType [] . expandType mid tcE . toType []) $ conTypes constr
  mapM_ (\f -> addLocalType (QI $ qualifyWith mid f) recType) $ conFields constr
  act <- checkDerive tc tys deriv
  return $ do
    cs <- act
    return (cs, NewtypeDecl spi tc vs constr deriv)
checkDecl (InfixDecl spi fix prec vs) =
  return $ return (Set.empty, InfixDecl spi fix prec vs)
checkDecl (TypeSig spi vs ty) =
  return $ return (Set.empty, TypeSig spi vs ty)
checkDecl (ExternalDataDecl spi tc vs) =
  return $ return (Set.empty, ExternalDataDecl spi tc vs)
checkDecl (TypeDecl spi tc vs ty) =
  return $ return (Set.empty, TypeDecl spi tc vs ty)
checkDecl (DefaultDecl spi tys) =
  return $ return (Set.empty, DefaultDecl spi tys)
checkDecl (DetSig spi is dty) =
  return $ return (Set.empty, DetSig spi is dty)

checkLocalDeclsTy :: [Decl PredType] -> DM (Set DetConstraint, [Decl (PredType, DetType)])
checkLocalDeclsTy ds = do
  act <- mapM checkLocalDecl ds
  (css, ds') <- unzip <$> sequence act
  return (Set.unions css, ds')
  where
    -- Like checkDecl, but does not qualify identifiers with the module identifier.
    checkLocalDecl :: Decl PredType -> DM (DM (Set DetConstraint, Decl (PredType, DetType)))
    checkLocalDecl (PatternDecl spi p rhs) = do
      v <- freshVar
      (cs, _, p') <- checkPat v p
      return $ do
        (cs', rhs') <- scoped (checkRhsTy v rhs)
        return (Set.union cs cs', PatternDecl spi p' rhs')
    checkLocalDecl d@(FunctionDecl spi pty f eqs) = do
      mid <- gets moduleIdent
      tcE <- gets tcEnv
      iE <- gets instEnv
      let unqualII (QI i) = QI $ qualify $ unqualify i
          unqualII (CI cls i) = CI cls $ qualify $ unqualify i
          unqualII (II cls tc i) = II cls tc $ qualify $ unqualify i
          is = map unqualII (declIdents iE mid tcE d)
      act <- checkFun is eqs
      return $ do
        (cs, dty, eqs') <- act
        return (cs, FunctionDecl spi (pty, dty) f eqs')
    checkLocalDecl (ExternalDecl spi vs) = do
      let go (Var pty@(PredType _ ty) i) = do
            let dty = mkArrowLike ty
            addLocalType (QI $ qualify i) dty
            dtyi <- instantiate dty
            return (Var (pty, dtyi) i)
      vs' <- mapM go vs
      return $ return (Set.empty, ExternalDecl spi vs')
    checkLocalDecl (FreeDecl spi vs) = do
      vs' <- forM vs $ \(Var pty i) -> do
        addLocalType (QI (qualify i)) (toDetSchema Any)
        return (Var (pty, Any) i)
      return $ return (Set.empty, FreeDecl spi vs')
    -- other cases can only be stuff like type signatures,
    -- which do not need to be checked in a special way
    checkLocalDecl d = checkDecl d

checkDerive :: Ident -> [TypeExpr] -> [QualIdent] -> DM (DM (Set DetConstraint))
checkDerive tc tys clss = do
  tcE <- gets tcEnv
  mid <- gets moduleIdent
  iE <- gets instEnv
  let goM cls (ClassMethod i _ (PredType _ ty) _ ann) = case ann of
        Just dty -> do
          addLocalType (II cls (qualifyWith mid tc) (zeroUniqueQual (qualifyLike cls i))) dty
          return []
        Nothing -> do
          v <- freshVar
          addLocalType (II cls (qualifyWith mid tc) (zeroUniqueQual (qualifyLike cls i))) (Forall [] (VarTy v))
          return [(cls, i, ty, v)]
      go cls = case qualLookupTypeInfo cls tcE of
        [TypeClass qcls' _ meths] -> concat <$> mapM (goM qcls) meths
          where qcls | isQualified qcls' = qcls'
                     | otherwise         = qualifyWith mid (unqualify qcls')
        _ -> internalError $ "DeterminismCheck.checkDerive: " ++ show cls ++ " not found"
  let clss' = case lookupInstInfo (qDataId, qualifyWith mid tc) iE of
                Just _  -> qDataId : clss
                Nothing -> clss
  info <- concat <$> mapM go clss'
  let ($$) f = f
  return $ Set.unions <$> forM info $$ \(cls, i, ty, v) -> do
    dty <- instantiate (mkArrowLike ty)
    let c1 = EqualType v dty
    cs <- forM tys $ \ty' ->
      case toInstanceIdentMaybe mid tcE cls ty' (QI (qualifyLike cls i)) of
        Nothing -> return Set.empty
        Just ii -> checkIdentInfo v True ii
    return (Set.insert c1 (Set.unions cs))

checkClassDecl :: Ident -> Decl PredType -> DM (DM (Set DetConstraint, Decl (PredType, DetType)))
checkClassDecl cls d@(FunctionDecl spi pty f eqs) = do
  mid <- gets moduleIdent
  clsEnv <- gets classEnv
  tcE <- gets tcEnv
  iE <- gets instEnv
  case lookupClassInfo (qualifyWith mid cls) clsEnv of
    Nothing -> internalError $ "checkClassDecl: " ++ show cls ++ " not found"
    Just (_, _) -> do
        -- Add class method `d` on global scope (happens in outer layer of checkFun)
        let is = map (toClassIdent (qualifyWith mid cls)) (declIdents iE mid tcE d)
        act <- checkFun is eqs
        return $ do
          (cs, dty, eqs') <- scoped act
          return (cs, FunctionDecl spi (pty, dty) f eqs')
checkClassDecl _ d = checkDecl d

checkInstanceDecl :: QualIdent -> InstanceType -> Decl PredType
                  -> DM (DM (Set DetConstraint, Decl (PredType, DetType)))
checkInstanceDecl cls ty d@(FunctionDecl spi pty f eqs) = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  iE <- gets instEnv
  case qualLookupTypeInfo cls tcE of
    [TypeClass qcls _ cm] -> do
      let mid' = fromMaybe mid (qidModule qcls)
          is = map (toInstanceIdent mid tcE (qualQualify mid' cls) ty) (declIdents iE mid' tcE d)
          addSig m@(ClassMethod qid _ _ _ _) = case methodDetSchemeAnn m of
            Nothing  -> return ()
            Just dty -> do
              modify (\s -> s { signatures = Map.insert qid (toDetExpr dty) (signatures s) } )
      mapM_ addSig cm
      act <- checkFun is eqs
      return $ do
        (cs, dty, eqs') <- scoped act
        return (cs, FunctionDecl spi (pty, dty) f eqs')
    _ -> internalError $ "checkInstanceDecl: " ++ show cls ++ " not found"
checkInstanceDecl _ _ d = checkDecl d

checkFun :: [IdentInfo] -> [Equation PredType]
         -> DM (DM (Set DetConstraint, DetType, [Equation (PredType, DetType)]))
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
    let c2 = if ov then Set.singleton (EqualType res Any) else Set.empty
    (cs, eqs') <- mapAndUnzipM (checkEquation args res) eqs
    return (Set.unions ([c1, c2] ++ cs), varTyped, eqs')

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

checkEquation :: [VarIndex] -> VarIndex -> Equation PredType
              -> DM (Set DetConstraint, Equation (PredType, DetType))
checkEquation args res (Equation spi lhs rhs) = do
  (cs1, is, lhs') <- checkLhs args lhs
  let demands = foldr (Set.insert . EqualType res . VarTy) Set.empty is -- for all demanded variables: res ~ alpha
  (cs2, rhs') <- scoped (checkRhsTy res rhs)
  return (Set.unions [demands, cs1, cs2], Equation spi lhs' rhs')

-- Returns a set of constraints and a list of variables that are demanded strictly
checkLhs :: [VarIndex] -> Lhs PredType -> DM (Set DetConstraint, [VarIndex], Lhs (PredType, DetType))
checkLhs vs (FunLhs spi f ps) = do
  (css, stricts, ps') <- unzip3 <$> zipWithM checkPat vs ps
  return (Set.unions css, map fst $ filter snd $ zip vs stricts, FunLhs spi f ps')
checkLhs [v1, v2] (OpLhs spi p1 f p2) = do
  (cs1, s1, p1') <- checkPat v1 p1
  (cs2, s2, p2') <- checkPat v2 p2
  return (Set.union cs1 cs2, map fst $ filter snd [(v1, s1), (v2, s2)], OpLhs spi p1' f p2')
checkLhs _ OpLhs {} = internalError "DeterminismCheck.genDetType: op with more than two arguments"
checkLhs vs (ApLhs spi lhs ps) = do
  let (vs1, vs2) = splitAt (length vs - length ps) vs
  (cs1, s1, lhs') <- checkLhs vs1 lhs
  (cs2, s2, ps') <- unzip3 <$> zipWithM checkPat vs2 ps
  return (Set.union cs1 (Set.unions cs2), s1 ++ map fst (filter snd (zip vs2 s2)), ApLhs spi lhs' ps')

checkPat :: VarIndex -> Pattern PredType
         -> DM (Set DetConstraint, Bool, Pattern (PredType, DetType))
checkPat v (VariablePattern spi pty i) = do
  unless (idName i == "_") $ addLocalType (QI (qualify i)) (toDetSchema (VarTy v))
  return (Set.empty, False, VariablePattern spi (pty, VarTy v) i)
checkPat v (ConstructorPattern spi pty qid ps) = do
  (css, _, ps') <- unzip3 <$> mapM (checkPat v) ps
  return (Set.unions css, True, ConstructorPattern spi (pty, VarTy v) qid ps')
checkPat v (InfixPattern spi pty p1 op p2) = do
  (cs1, _, p1') <- checkPat v p1
  (cs2, _, p2') <- checkPat v p2
  return (Set.union cs1 cs2, True, InfixPattern spi (pty, VarTy v) p1' op p2')
checkPat v (ParenPattern spi p) = do
  (cs, dmd, p') <- checkPat v p
  return (cs, dmd, ParenPattern spi p')
checkPat v (RecordPattern spi pty qid fs) = do
  (css, fs') <- mapAndUnzipM (checkPatField v) fs
  return (Set.unions css, True, RecordPattern spi (pty, VarTy v) qid fs')
checkPat v (TuplePattern spi ps) = do
  (css, _, ps') <- unzip3 <$> mapM (checkPat v) ps
  return (Set.unions css, True, TuplePattern spi ps')
checkPat v (ListPattern spi pty ps) = do
  (css, _, ps') <- unzip3 <$> mapM (checkPat v) ps
  return (Set.unions css, True, ListPattern spi (pty, VarTy v) ps')
checkPat v (AsPattern spi i p) = do
  addLocalType (QI (qualify i)) (toDetSchema (VarTy v))
  (cs, dmd, p') <- checkPat v p
  return (cs, dmd, AsPattern spi i p')
checkPat v (LazyPattern spi p) = do
  (cs, _, p') <- checkPat v p
  return (cs, False, LazyPattern spi p')
checkPat v (FunctionPattern spi pty@(PredType preds ty) i ps) = do
  w <- freshVar
  vs <- replicateM (length ps) freshVar
  let c1 = AppliedType v w (map VarTy vs)
  let c2 = EqualType w (foldr (DetArrow . VarTy) (VarTy v) vs)
  (css, _, ps') <- unzip3 <$> zipWithM checkPat vs ps
  let pty' = PredType preds (foldr (TypeArrow . typeOf) ty ps)
  cs1 <- checkVar w pty' i
  -- return True, because we assume functional pattern to be demanded
  let p' = FunctionPattern spi (pty, VarTy v) i ps'
  return (Set.insert c1 (Set.insert c2 (Set.unions (cs1:css))), True, p')
checkPat v (InfixFuncPattern spi pty@(PredType preds ty) p1 i p2) = do
  w <- freshVar
  v1 <- freshVar
  v2 <- freshVar
  let c1 = AppliedType v w (map VarTy [v1, v2])
  let c2 = EqualType w (foldr (DetArrow . VarTy) (VarTy v) [v1, v2])
  (cs1, _, p1') <- checkPat v1 p1
  (cs2, _, p2') <- checkPat v2 p2
  let pty' = PredType preds (foldr (TypeArrow . typeOf) ty [p1, p2])
  cs3 <- checkVar w pty' i
  let p' = InfixFuncPattern spi (pty, VarTy v) p1' i p2'
  -- return True, because we assume functional pattern to be demanded
  return (Set.insert c1 (Set.insert c2 (Set.unions [cs1, cs2, cs3])), True, p')
checkPat v (LiteralPattern spi pty lit) =
  return (Set.empty, True, LiteralPattern spi (pty, VarTy v) lit)
checkPat v (NegativePattern spi pty lit) =
  return (Set.empty, True, NegativePattern spi (pty, VarTy v) lit)

checkPatField :: VarIndex -> Field (Pattern PredType)
              -> DM (Set DetConstraint, Field (Pattern (PredType, DetType)))
checkPatField v (Field spi qid p) = do
  (cs, _, p') <- checkPat v p
  return (cs, Field spi qid p')

checkRhsTy :: VarIndex -> Rhs PredType
           -> DM (Set DetConstraint, Rhs (PredType, DetType))
checkRhsTy v (SimpleRhs spi li e ds) = do
  (cs1, ds') <- checkLocalDeclsTy ds
  (cs2, e') <- scoped (checkExprTy v e)
  return (Set.union cs1 cs2, SimpleRhs spi li e' ds')
checkRhsTy v (GuardedRhs spi li gs ds) = do
  (cs1, ds')  <- checkLocalDeclsTy ds
  (css, gs') <- mapAndUnzipM (scoped . checkCondExprTy v) gs
  return (Set.unions (cs1:css), GuardedRhs spi li gs' ds')

checkCondExprTy :: VarIndex -> CondExpr PredType
                -> DM (Set DetConstraint, CondExpr (PredType, DetType))
checkCondExprTy v (CondExpr spi e1 e2) = do
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  return (Set.union cs1 cs2, CondExpr spi e1' e2')

checkExprTy :: VarIndex -> Expression PredType
            -> DM (Set DetConstraint, Expression (PredType, DetType))
checkExprTy v (Variable spi dty i) = do
  cs <- checkVar v dty i
  return (cs, Variable spi (dty, VarTy v) i)
checkExprTy v (Typed spi e ty) = do
  (cs, e') <- checkExprTy v e
  return (cs, Typed spi e' ty)
checkExprTy v (Apply spi e1 e2) = do
  v1 <- freshVar
  (cs1, e1') <- checkExprTy v1 e1
  v2 <- freshVar
  (cs2, e2') <- checkExprTy v2 e2
  let c1 = AppliedType v v1 [VarTy v2]
      c2 = EqualType v1 (DetArrow (VarTy v2) (VarTy v))
  return (Set.insert c1 (Set.insert c2 (Set.union cs1 cs2)), Apply spi e1' e2')
checkExprTy v (InfixApply spi e1 op e2) = do
  v1 <- freshVar
  (cs1, e1') <- checkExprTy v1 e1
  v2 <- freshVar
  (cs2, e2') <- checkExprTy v2 e2
  v3 <- freshVar
  (cs3, op') <- checkInfixOpTy v3 op
  let c1 = AppliedType v v3 [VarTy v1, VarTy v2]
      c2 = EqualType v3 (DetArrow (VarTy v1) (DetArrow (VarTy v2) (VarTy v)))
  return (Set.insert c1 (Set.insert c2 (Set.unions [cs1, cs2, cs3])), InfixApply spi e1' op' e2')
checkExprTy v (Paren spi e) = do
  (cs, e') <- checkExprTy v e
  return (cs, Paren spi e')
checkExprTy v (Constructor spi pty@(PredType _ ty) qid) = do
  let dty = foldr DetArrow Det (replicate (arrowArity ty) Det)
  return (Set.singleton (EqualType v dty), Constructor spi (pty, dty) qid)
checkExprTy v (Tuple spi es) = do
  (css, es') <- mapAndUnzipM (checkExprTy v) es
  return (Set.unions css, Tuple spi es')
checkExprTy v (List spi pty es) = do
  (css, es') <- mapAndUnzipM (checkExprTy v) es
  return (Set.unions css, List spi (pty, VarTy v) es')
checkExprTy v (ListCompr spi e qs) = do
  (cs, qs', e') <- checkStmts v e qs
  return (cs, ListCompr spi e' qs')
checkExprTy v ee@(EnumFrom spi e) = do
  let ety = typeOf e
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety eety)
  (cs1, e') <- checkExprTy v e
  cs2 <- checkVar v enumTy qEnumFromId
  return (Set.union cs1 cs2, EnumFrom spi e')
checkExprTy v ee@(EnumFromThen spi e1 e2) = do
  let ety = typeOf e1
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety (TypeArrow ety eety))
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  cs3 <- checkVar v enumTy qEnumFromThenId
  return (Set.union (Set.union cs1 cs2) cs3, EnumFromThen spi e1' e2')
checkExprTy v ee@(EnumFromTo spi e1 e2) = do
  let ety = typeOf e1
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety (TypeArrow ety eety))
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  cs3 <- checkVar v enumTy qEnumFromToId
  return (Set.union (Set.union cs1 cs2) cs3, EnumFromTo spi e1' e2')
checkExprTy v ee@(EnumFromThenTo spi e1 e2 e3) = do
  let ety = typeOf e1
      eety = typeOf ee
      enumTy = PredType emptyPredSet (TypeArrow ety (TypeArrow ety (TypeArrow ety eety)))
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  (cs3, e3') <- checkExprTy v e3
  cs4 <- checkVar v enumTy qEnumFromThenToId
  return (Set.union (Set.union (Set.union cs1 cs2) cs3) cs4, EnumFromThenTo spi e1' e2' e3')
checkExprTy v (Record spi pty qid fs) = do
  (css, fs') <- mapAndUnzipM (checkExprField v) fs
  return (Set.unions css, Record spi (pty, VarTy v) qid fs')
checkExprTy v (RecordUpdate spi e fs) = do
  (cs, e') <- checkExprTy v e
  (css, fs') <- mapAndUnzipM (checkExprField v) fs
  return (Set.union cs (Set.unions css), RecordUpdate spi e' fs')
checkExprTy v (Lambda spi ps e) = scoped $ do
  vs <- replicateM (length ps) freshVar
  (css, stricts, ps') <- unzip3 <$> zipWithM checkPat vs ps
  v' <- freshVar
  (cs1, e') <- checkExprTy v' e
  let c = EqualType v (foldr (DetArrow . VarTy) (VarTy v') vs)
      cs' = foldr ((Set.insert . EqualType v' . VarTy) . fst)
              (Set.insert c (Set.unions (cs1:css)))
              (filter snd $ zip vs stricts)
  return (cs', Lambda spi ps' e')
checkExprTy v (Let spi li ds e) = scoped $ do
  (cs1, ds') <- checkLocalDeclsTy ds
  (cs2, e') <- checkExprTy v e
  return (Set.union cs1 cs2, Let spi li ds' e')
checkExprTy v (Do spi li ss e) = do
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
  cs1 <- if any (stmtCanFail tcE) ss
    then checkVar v failTy qFailId
    else return Set.empty
  cs2 <- checkVar v bindTy qBindId
  (cs3, ss', e') <- checkStmts v e ss
  return (Set.unions [cs1, cs2, cs3], Do spi li ss' e')
checkExprTy v (LeftSection spi e op) = do
  v1 <- freshVar
  (cs1, e') <- checkExprTy v1 e
  v2 <- freshVar
  v3 <- freshVar
  (cs3, op') <- checkInfixOpTy v3 op
  let c1 = AppliedType v v3 [VarTy v1, VarTy v2]
      c2 = EqualType v3 (DetArrow (VarTy v1) (DetArrow (VarTy v2) (VarTy v)))
  return (Set.insert c1 (Set.insert c2 (Set.unions [cs1, cs3])), LeftSection spi e' op')
checkExprTy v (RightSection spi op e) = do
  v1 <- freshVar
  v2 <- freshVar
  (cs2, e') <- checkExprTy v2 e
  v3 <- freshVar
  (cs3, op') <- checkInfixOpTy v3 op
  let c1 = AppliedType v v3 [VarTy v1, VarTy v2]
      c2 = EqualType v3 (DetArrow (VarTy v1) (DetArrow (VarTy v2) (VarTy v)))
  return (Set.insert c1 (Set.insert c2 (Set.unions [cs2, cs3])), RightSection spi op' e')
checkExprTy v (IfThenElse spi e1 e2 e3) = do
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  (cs3, e3') <- checkExprTy v e3
  return (Set.unions [cs1, cs2, cs3], IfThenElse spi e1' e2' e3')
checkExprTy v (Case spi li ct e bs) = do
  (cs1, e') <- checkExprTy v e
  (css, bs') <- mapAndUnzipM (scoped . checkAlt v) bs
  return (Set.unions (cs1:css), Case spi li ct e' bs')
-- Once again, next two are to be deterministic by design,
-- since their pattern variants are needed to be deterministic.
-- Thus we skip adding a dependency on numFreeIdent.
checkExprTy v (UnaryMinus spi e) = do
  (cs, e') <- checkExprTy v e
  return (cs, UnaryMinus spi e')
checkExprTy v (Literal spi pty l) =
  return (Set.singleton (EqualType v Det), Literal spi (pty, Det) l)

checkAlt :: VarIndex -> Alt PredType -> DM (Set DetConstraint, Alt (PredType, DetType))
checkAlt v (Alt spi p rhs) = do
  (cs1, _, p') <- checkPat v p
  (cs2, rhs') <- scoped (checkRhsTy v rhs)
  return (Set.union cs1 cs2, Alt spi p' rhs')

checkStmts :: VarIndex -> Expression PredType -> [Statement PredType]
           -> DM (Set DetConstraint, [Statement (PredType, DetType)], Expression (PredType, DetType))
checkStmts v e [] = do
  (cs, e') <- checkExprTy v e
  return (cs, [], e')
checkStmts v e (s:ss) = case s of
  StmtDecl spi li ds -> scoped $ do
    (cs1, ds') <- checkLocalDeclsTy ds
    (cs2, ss', e') <- checkStmts v e ss
    return (Set.union cs1 cs2, StmtDecl spi li ds' : ss', e')
  StmtExpr spi e2 -> do
    (cs1, e2') <- checkExprTy v e2
    (cs2, ss', e') <- checkStmts v e ss
    return (Set.union cs1 cs2, StmtExpr spi e2' : ss', e')
  StmtBind spi p e2 -> do
    (cs1, e2') <- checkExprTy v e2
    scoped $ do
      (cs2, _, p') <- checkPat v p
      (cs3, ss', e') <- checkStmts v e ss
      return (Set.union cs1 (Set.union cs2 cs3), StmtBind spi p' e2' : ss', e')

checkExprField :: VarIndex -> Field (Expression PredType)
               -> DM (Set DetConstraint, Field (Expression (PredType, DetType)))
checkExprField v (Field spi qid e) = do
  (cs, e') <- checkExprTy v e
  return (cs, Field spi qid e')

checkInfixOpTy :: VarIndex -> InfixOp PredType -> DM (Set DetConstraint, InfixOp (PredType, DetType))
checkInfixOpTy v (InfixOp ty i) = do
  cs <- checkVar v ty i
  return (cs, InfixOp (ty, VarTy v) i)
checkInfixOpTy v (InfixConstr pty@(PredType _ ty) qid) = do
  let dty = foldr DetArrow Det (replicate (arrowArity ty) Det)
  return (Set.singleton (EqualType v dty), InfixConstr (pty, dty) qid)

checkVar :: VarIndex -> PredType -> QualIdent -> DM (Set DetConstraint)
checkVar v (PredType _ ty) i = do
  cE <- gets classEnv
  mid <- gets moduleIdent
  mii <- variableFreeIdent i ty
  vEnv <- gets valueEnv
  let (preds, mcls) = case qualLookupValueUnique mid i vEnv of
        [Value _ Nothing    _ (ForAll _ (PredType preds' ty'))]
          -> (subst (matchType ty' ty idSubst) preds', Nothing)
        [Value _ (Just cls) _ (ForAll _ (PredType preds' ty'))]
          -- Remove the implied class predicate, since we do not need to check it when
          -- checking the method of a class.
          -> (subst (matchType ty' ty idSubst) (Set.delete (Pred cls (TypeVariable 0)) preds'), Just cls)
          -- Local identifier.
        _ -> (emptyPredSet, Nothing)
  detCtx <- andM checkPred (Set.toList preds)
  case mii of
    -- Nothing means this is a class method on a type variable.
    Nothing -> case mcls of
      Nothing -> internalError $ "DeterminismCheck.checkVar: class expected for" ++ show i
      Just cls | detCtx    -> case lookupClassInfo cls cE  of
                    Just (_, mthds) ->
                      -- Check if the class method has an annotation use that type if it exists.
                      -- Otherwise, we conservatively assume that the method is non-deterministic.
                      let go m | unqualify i == fst4 m = case fth4 m of
                                    Nothing -> return $ Set.singleton $ EqualType v Any
                                    Just dty -> Set.singleton . EqualType v <$> instantiate dty
                              | otherwise = return Set.empty
                      -- Exaxtly one of the sets will be non-empty
                      in Set.unions <$> mapM go mthds
                    _ -> internalError $ "DeterminismCheck.checkVar: " ++ render (pPrint cls) ++ " not found"
               | otherwise -> return $ Set.singleton $ EqualType v Any
    -- Concrete identifier or instance method of a known type constructor.
    Just ii   -> checkIdentInfo v detCtx ii

checkIdentInfo :: VarIndex -> Bool -> IdentInfo -> DM (Set DetConstraint)
checkIdentInfo v detCtx ii = do
  lcl <- gets localDetEnv
  ext <- gets detEnv
  case Map.lookup ii ext of
    Just ty'
      | detCtx    -> Set.singleton . EqualType v <$> instantiate ty'
      | otherwise -> return $ Set.singleton $ EqualType v Any
    Nothing -> case lookupNestDetEnv ii lcl of
      Just ty'
        | detCtx    -> Set.singleton . EqualType v <$> instantiate ty'
        | otherwise -> return $ Set.singleton $ EqualType v Any
      Nothing
        | QI qi <- ii,
          idName (qidIdent qi) == "_"
                    -> return $ Set.singleton $ EqualType v Any
        | otherwise -> internalError $ "checkIdentInfo: " ++ render (pPrint ii) ++ " not found in \n:"
                                                          ++ render (pPrint (Map.keys ext))

checkPred :: Pred -> DM Bool
checkPred (Pred cls ty) = do
  mid <- gets moduleIdent
  clsEnv <- gets classEnv
  lcl <- gets localDetEnv
  ext <- gets detEnv
  let qcls = qualQualify mid cls
  case lookupClassInfo qcls clsEnv of
    Nothing -> internalError $ "checkPred: " ++ render (pPrint cls) ++ " not found"
    Just (_, meths) -> flip andM meths $ \(m, _, _, _) ->
      -- Similar to the story in `predFreeIdents`, we do not need to check
      -- any predicates implied by the used instancehere as well.
      case unapplyType True ty of
        (TypeConstructor tc, _) ->
          let qtc = case tc of
                      QualIdent _ (Just _) _  -> tc
                      QualIdent _ Nothing idt
                        | idt == listId
                        || idt == unitId
                        || idt == arrowId
                        || idt == listId -> qualifyWith preludeMIdent idt
                        | otherwise      -> qualifyWith mid idt
              ii = II qcls qtc (zeroUniqueQual (qualifyLike qcls m))
          in case lookupNestDetEnv ii lcl of
            Just sc -> return (notAnyType sc)
            Nothing -> case Map.lookup ii ext of
              Just sc -> return (notAnyType sc)
              Nothing -> internalError $ "checkPred: " ++ render (pPrint ii) ++ " not found."
        _ -> return False
  where
    notAnyType (Forall _ ty') = notAnyTypeTy ty'
    notAnyTypeTy (VarTy _) = True
    notAnyTypeTy Det = True
    notAnyTypeTy (DetArrow ty1 ty2) = notAnyTypeTy ty1 && notAnyTypeTy ty2
    notAnyTypeTy Any = False

-- -----------------------------------------------------------------------------
-- * Solving determinism constraints
-- -----------------------------------------------------------------------------

-- Solve by maintaining equivalence classes of variables using a union-find implementation.
-- We also keep a list that maps the highest element of each eqivalent class
-- to a non-variable determinism type if one is known.
-- TODO: re-run AppliedType checks after an applied type changes anything.
solveConstraints :: Set DetConstraint -> DM (Map VarIndex DetType)
solveConstraints constraints = do
  return $ runEquivM id max $ doSolve Map.empty Map.empty constraints

doSolve :: Map VarIndex DetType             -- ^ Substitution
        -> Map VarIndex (Set DetConstraint) -- ^ Re-runnable AppliedType constraints
        -> Set DetConstraint                -- ^ Constraints
        -> EquivM s VarIndex VarIndex (Map VarIndex DetType)
doSolve current reRun constraints = case Set.minView constraints of
  Nothing -> mkSubstitution current
  Just (c, cs) -> case c of
    EqualType v (VarTy w)
      | v == w    -> doSolve current reRun cs
      | otherwise -> do
          d1 <- classDesc v
          d2 <- classDesc w
          equate v w
          case (Map.lookup d1 current, Map.lookup d2 current) of
            (Just dty1, Just dty2) ->
              let (dty', cs') = unify dty1 dty2 cs
              in doSolve (extendSubst (max d1 d2) dty' current) reRun cs'
            (Just dty1, Nothing) ->
              doSolve (extendSubst (max d1 d2) dty1 current) reRun cs
            (Nothing, Just dty2) ->
              doSolve (extendSubst (max d1 d2) dty2 current) reRun cs
            (Nothing, Nothing) ->
              doSolve current reRun cs
    EqualType v dty2 -> do
          d1 <- classDesc v
          case Map.lookup d1 current of
            Nothing -> doSolve (extendSubst d1 dty2 current) reRun cs
            Just dty1 ->
              let (dty', cs') = unify dty1 dty2 cs
              in doSolve (extendSubst d1 dty' current) reRun cs'
    AppliedType v w tys -> do
      e <- equivalent v w
      d1 <- classDesc v
      d2 <- classDesc w
      if e
        then doSolve (extendSubst (max d1 d2) Any current) reRun cs
        else case (Map.lookup d1 current, Map.lookup d2 current) of
          (Just dty1, Just dty2) ->
            let vs = d1 : d2 : vars tys
                (dty1', cs') = unify dty1 (applyDetType dty2 tys) cs
                reRun' = foldr (\v' -> Map.insertWith Set.union v' (Set.singleton c))
                          reRun vs
                vsCons = foldr (\v' s -> Set.union s $ Map.findWithDefault Set.empty v' reRun) cs' vs
            in if dty1 == dty1'
              then doSolve current reRun' cs'
              else doSolve current reRun' (Set.insert (EqualType d1 dty1') vsCons)
          (Just dty1, Nothing) ->
            let dty2 = foldr DetArrow dty1 tys
                reRun' = foldr (\v' -> Map.insertWith Set.union v' (Set.singleton c))
                          reRun (d1 : d2 : vars tys)
            in doSolve current reRun' (Set.insert (EqualType d2 dty2) cs)
          (Nothing, Just dty2) ->
            let dty1 = applyDetType dty2 tys
                reRun' = foldr (\v' -> Map.insertWith Set.union v' (Set.singleton c))
                          reRun (d1 : d2 : vars tys)
            in doSolve current reRun' (Set.insert (EqualType d1 dty1) cs)
          (Nothing, Nothing) ->
            let reRun' = foldr (\v' -> Map.insertWith Set.union v' (Set.singleton c))
                          reRun (d1 : d2 : vars tys)
            in doSolve current reRun' cs
  where
    unify :: DetType -> DetType -> Set DetConstraint -> (DetType, Set DetConstraint)
    unify (VarTy v) (VarTy w) cs'
      | v == w    = (VarTy v, cs')
      | otherwise = (VarTy v, Set.insert (EqualType v (VarTy w)) cs')
    unify (VarTy v) ty cs' = (ty, Set.insert (EqualType v ty) cs')
    unify ty (VarTy v) cs' = (ty, Set.insert (EqualType v ty) cs')
    unify Det Det cs' = (Det, cs')
    unify Any _ cs' = (Any, cs')
    unify _ Any cs' = (Any, cs')
    unify (DetArrow ty1 ty2) (DetArrow ty1' ty2') cs' =
      let (new1, cs'1) = unify ty1 ty1' cs'
          (new2, cs'2) = unify ty2 ty2' cs'1
      in (DetArrow new1 new2, cs'2)
    unify (DetArrow ty1 ty2) Det cs' =
      unify (DetArrow ty1 ty2) (DetArrow Det Det) cs'
    unify Det (DetArrow ty1 ty2) cs' =
      unify (DetArrow Det Det) (DetArrow ty1 ty2) cs'

    vars = concatMap vars'
    vars' (VarTy v) = [v]
    vars' (DetArrow ty1 ty2) = vars' ty1 ++ vars' ty2
    vars' _ = []

extendSubst :: VarIndex -> DetType -> Map VarIndex DetType -> Map VarIndex DetType
extendSubst v (VarTy w) | v == w = id
extendSubst v dty = Map.insert v dty

-- For each variable that is not the maximal element in its equivalence class,
-- look up if a determinism type is known for the maximal element.
-- If it is, extend the substitution with the variable mapped to the determinism type.
-- Otherwise, extend the substitution with the variable mapped to the maximal element.
mkSubstitution :: Map VarIndex DetType
               -> EquivM s VarIndex VarIndex (Map VarIndex DetType)
mkSubstitution solved = (>>=) values $ flip foldM solved $ \current v -> do
  c <- classDesc v
  if v == c
    then return current
    else
      let dty = case Map.lookup c current of
                  Nothing   -> VarTy c
                  Just dty' -> dty'
      in return $ extendSubst v dty
                $ Map.map (`substDetTy` Map.singleton v dty) current

applyDetType :: DetType -> [DetType] -> DetType
applyDetType ty [] = ty
applyDetType Any _ = Any
applyDetType (DetArrow (VarTy v) ty2) (ty:rest) =
  applyDetType (substDetTy ty2 (Map.singleton v ty)) rest
applyDetType (DetArrow ty1 ty2) (VarTy v:rest) =
  applyDetType (DetArrow ty1 ty2) (ty1 : map (`substDetTy` Map.singleton v ty1) rest)
applyDetType (DetArrow ty1 ty2) (ty:rest) = case ty `moreSpecific` ty1 of
  Just s -> applyDetType (substDetTy ty2 s) rest
  Nothing -> Any
applyDetType ty tys = internalError $ "applyDetType: not enough arguments " ++ show ty ++ " @ " ++ show tys

-- Both `moreSpecific` and `lessSpecific` return `Nothing` if
-- the two types are not in the desired relation.
-- Otherwise they return `Just s`,
-- where `s` is a substitution that maps variables
-- from the second onto the first type.
moreSpecific :: DetType -> DetType -> Maybe (Map VarIndex DetType)
moreSpecific ty (VarTy v) = Just (Map.singleton v ty)
moreSpecific (DetArrow ty1 ty2) (DetArrow ty1' ty2') = do
  s1 <- ty1' `moreSpecific` ty1
  s2 <- ty2 `moreSpecific` ty2'
  return (Map.union s1 s2)
moreSpecific Det Any = Just Map.empty
moreSpecific Det Det = Just Map.empty
moreSpecific Any Any = Just Map.empty
moreSpecific _ _ = Nothing

lessSpecific :: DetType -> DetType -> Maybe (Map VarIndex DetType)
lessSpecific ty (VarTy v) = Just (Map.singleton v ty)
lessSpecific (DetArrow ty1 ty2) (DetArrow ty1' ty2') = do
  s1 <- ty1' `lessSpecific` ty1
  s2 <- ty2 `lessSpecific` ty2'
  return (Map.union s1 s2)
lessSpecific Any Det = Just Map.empty
lessSpecific Det Det = Just Map.empty
lessSpecific Any Any = Just Map.empty
lessSpecific _ _ = Nothing

-- -----------------------------------------------------------------------------
-- Fixing stuff after inference
-- -----------------------------------------------------------------------------

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

fixDecl :: Map VarIndex DetType -> Decl (PredType, DetType)
        -> DM (Decl (PredType, DetType))
fixDecl sub (FunctionDecl spi pty f eqs) = do
  eqs' <- mapM (fixEquation sub) eqs
  return (FunctionDecl spi pty f eqs')
fixDecl sub (PatternDecl spi p rhs) = do
  rhs' <- fixRhs sub rhs
  p' <- fixPat sub p
  return (PatternDecl spi p' rhs')
fixDecl sub (ClassDecl spi li ctx cls v ds) = do
  ds' <- mapM (fixDecl sub) ds
  return (ClassDecl spi li ctx cls v ds')
fixDecl sub (InstanceDecl spi li ctx cls ty ds) = do
  ds' <- mapM (fixDecl sub) ds
  return (InstanceDecl spi li ctx cls ty ds')
fixDecl sub (ExternalDecl spi vs) = do
  vs' <- mapM (fixVar sub) vs
  return (ExternalDecl spi vs')
fixDecl _ d = return d

fixEquation :: Map VarIndex DetType -> Equation (PredType, DetType)
            -> DM (Equation (PredType, DetType))
fixEquation sub (Equation spi lhs rhs) = do
  rhs' <- fixRhs sub rhs
  lhs' <- fixLhs sub lhs
  return (Equation spi lhs' rhs')

fixLhs :: Map VarIndex DetType -> Lhs (PredType, DetType)
       -> DM (Lhs (PredType, DetType))
fixLhs sub (FunLhs spi f ps) = do
  ps' <- mapM (fixPat sub) ps
  return (FunLhs spi f ps')
fixLhs sub (OpLhs spi p1 op p2) = do
  p1' <- fixPat sub p1
  p2' <- fixPat sub p2
  return (OpLhs spi p1' op p2')
fixLhs sub (ApLhs spi lhs ps) = do
  lhs' <- fixLhs sub lhs
  ps' <- mapM (fixPat sub) ps
  return (ApLhs spi lhs' ps')

fixRhs :: Map VarIndex DetType -> Rhs (PredType, DetType)
       -> DM (Rhs (PredType, DetType))
fixRhs sub (SimpleRhs spi li e ds) = do
  e' <- fixExpr sub e
  ds' <- mapM (fixDecl sub) ds
  return (SimpleRhs spi li e' ds')
fixRhs sub (GuardedRhs spi li gs ds) = do
  gs' <- mapM (fixCondExpr sub) gs
  ds' <- mapM (fixDecl sub) ds
  return (GuardedRhs spi li gs' ds')

-- This is sufficient for pattern here.
fixPat :: Map VarIndex DetType -> Pattern (PredType, DetType)
       -> DM (Pattern (PredType, DetType))
fixPat sub p = return $ fmap (second (`substDetTy` sub)) p

fixVar :: Map VarIndex DetType -> Var (PredType, DetType)
       -> DM (Var (PredType, DetType))
fixVar sub (Var (pty, dty) v) = do
  dE <- gets detEnv
  mid <- gets moduleIdent
  case Map.lookup (QI (qualifyWith mid v)) dE of
    Just sc -> do
      dty' <- instantiate sc
      return (Var (pty, dty') v)
    Nothing   -> return (Var (pty, dty `substDetTy` sub) v)

fixCondExpr :: Map VarIndex DetType -> CondExpr (PredType, DetType)
            -> DM (CondExpr (PredType, DetType))
fixCondExpr sub (CondExpr spi e1 e2) = do
  e1' <- fixExpr sub e1
  e2' <- fixExpr sub e2
  return (CondExpr spi e1' e2')

fixExpr :: Map VarIndex DetType -> Expression (PredType, DetType)
        -> DM (Expression (PredType, DetType))
fixExpr sub (Variable spi (pty, dty) i) = do
  dE <- gets detEnv
  ii <- variableFreeIdent i (unpredType pty)
  case ii >>= (`Map.lookup` dE) of
    Just sc -> do
      dty' <- instantiate sc
      return (Variable spi (pty, dty') i)
    Nothing -> return (Variable spi (pty, dty `substDetTy` sub) i)
fixExpr sub (Typed spi e ty) = do
  e' <- fixExpr sub e
  return (Typed spi e' ty)
fixExpr sub (Apply spi e1 e2) = do
  e1' <- fixExpr sub e1
  e2' <- fixExpr sub e2
  return (Apply spi e1' e2')
fixExpr sub (InfixApply spi e1 op e2) = do
  e1' <- fixExpr sub e1
  op' <- fixInfixOp sub op
  e2' <- fixExpr sub e2
  return (InfixApply spi e1' op' e2')
fixExpr sub (Paren spi e) = do
  e' <- fixExpr sub e
  return (Paren spi e')
fixExpr _ e@Constructor {} =
  return e
fixExpr sub (Tuple spi es) = do
  es' <- mapM (fixExpr sub) es
  return (Tuple spi es')
fixExpr sub (List spi (pty, dty) es) = do
  es' <- mapM (fixExpr sub) es
  return (List spi (pty, dty `substDetTy` sub) es')
fixExpr sub (ListCompr spi e qs) = do
  e' <- fixExpr sub e
  qs' <- mapM (fixStmt sub) qs
  return (ListCompr spi e' qs')
fixExpr sub (EnumFrom spi e) = do
  e' <- fixExpr sub e
  return (EnumFrom spi e')
fixExpr sub (EnumFromThen spi e1 e2) = do
  e1' <- fixExpr sub e1
  e2' <- fixExpr sub e2
  return (EnumFromThen spi e1' e2')
fixExpr sub (EnumFromTo spi e1 e2) = do
  e1' <- fixExpr sub e1
  e2' <- fixExpr sub e2
  return (EnumFromTo spi e1' e2')
fixExpr sub (EnumFromThenTo spi e1 e2 e3) = do
  e1' <- fixExpr sub e1
  e2' <- fixExpr sub e2
  e3' <- fixExpr sub e3
  return (EnumFromThenTo spi e1' e2' e3')
fixExpr sub (Record spi (pty, dty) qid fs) = do
  fs' <- mapM (fixExprField sub) fs
  return (Record spi (pty, dty `substDetTy` sub) qid fs')
fixExpr sub (RecordUpdate spi e fs) = do
  e' <- fixExpr sub e
  fs' <- mapM (fixExprField sub) fs
  return (RecordUpdate spi e' fs')
fixExpr sub (Lambda spi ps e) = do
  ps' <- mapM (fixPat sub) ps
  e' <- fixExpr sub e
  return (Lambda spi ps' e')
fixExpr sub (Let spi li ds e) = do
  ds' <- mapM (fixDecl sub) ds
  e' <- fixExpr sub e
  return (Let spi li ds' e')
fixExpr sub (Do spi li ss e) = do
  ss' <- mapM (fixStmt sub) ss
  e' <- fixExpr sub e
  return (Do spi li ss' e')
fixExpr sub (LeftSection spi e op) = do
  e' <- fixExpr sub e
  op' <- fixInfixOp sub op
  return (LeftSection spi e' op')
fixExpr sub (RightSection spi op e) = do
  op' <- fixInfixOp sub op
  e' <- fixExpr sub e
  return (RightSection spi op' e')
fixExpr sub (IfThenElse spi e1 e2 e3) = do
  e1' <- fixExpr sub e1
  e2' <- fixExpr sub e2
  e3' <- fixExpr sub e3
  return (IfThenElse spi e1' e2' e3')
fixExpr sub (Case spi li ct e bs) = do
  e' <- fixExpr sub e
  bs' <- mapM (fixAlt sub) bs
  return (Case spi li ct e' bs')
fixExpr sub (UnaryMinus spi e) = do
  e' <- fixExpr sub e
  return (UnaryMinus spi e')
fixExpr _ e@Literal {} = do
  return e

fixInfixOp :: Map VarIndex DetType -> InfixOp (PredType, DetType)
           -> DM (InfixOp (PredType, DetType))
fixInfixOp sub (InfixOp (pty, dty) i) = do
  dE <- gets detEnv
  ii <- variableFreeIdent i (unpredType pty)
  case ii >>= (`Map.lookup` dE) of
    Just sc -> do
      dty' <- instantiate sc
      return (InfixOp (pty, dty') i)
    Nothing -> return (InfixOp (pty, dty `substDetTy` sub) i)
fixInfixOp _ op@InfixConstr {} =
  return op

fixAlt :: Map VarIndex DetType -> Alt (PredType, DetType)
       -> DM (Alt (PredType, DetType))
fixAlt sub (Alt spi p rhs) = do
  p' <- fixPat sub p
  rhs' <- fixRhs sub rhs
  return (Alt spi p' rhs')

fixStmt :: Map VarIndex DetType -> Statement (PredType, DetType)
        -> DM (Statement (PredType, DetType))
fixStmt sub (StmtExpr spi e) = do
  e' <- fixExpr sub e
  return (StmtExpr spi e')
fixStmt sub (StmtDecl spi li ds) = do
  ds' <- mapM (fixDecl sub) ds
  return (StmtDecl spi li ds')
fixStmt sub (StmtBind spi p e) = do
  p' <- fixPat sub p
  e' <- fixExpr sub e
  return (StmtBind spi p' e')

fixExprField :: Map VarIndex DetType -> Field (Expression (PredType, DetType))
             -> DM (Field (Expression (PredType, DetType)))
fixExprField sub (Field spi qid e) = do
  e' <- fixExpr sub e
  return (Field spi qid e')

-- -----------------------------------------------------------------------------
-- * Collecting free identifiers
-- -----------------------------------------------------------------------------

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
  freeIdents (DataDecl _ _ _ constrs deriv) = do
    mid <- gets moduleIdent
    tcE <- gets tcEnv
    let tys = map (fromType [] . expandType mid tcE . toType []) $ concatMap conTypes constrs
    dataFreeIdents tys deriv
  freeIdents (NewtypeDecl _ _ _ constr ty) =do
    mid <- gets moduleIdent
    tcE <- gets tcEnv
    let tys = map (fromType [] . expandType mid tcE . toType []) $ conTypes constr
    dataFreeIdents tys ty
  freeIdents _ = return Set.empty

dataFreeIdents :: [TypeExpr] -> [QualIdent] -> DM (Set IdentInfo)
dataFreeIdents tys clss = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  exts <- gets extensions
  let clss' | NoDataDeriving `Set.member` exts = clss
            | otherwise = qDataId : clss
      css = flip map clss' $ \cls ->
        flip map tys $ \ty ->
          case qualLookupTypeInfo cls tcE of
            [TypeClass qcls' _ meths] -> flip map meths $ \(ClassMethod i _ _ _ _) ->
              let qcls | isQualified qcls' = qcls'
                       | otherwise = qualifyWith mid (unqualify qcls')
              in toInstanceIdentMaybe mid tcE qcls ty (QI (qualifyLike qcls i))
            _ -> internalError $ "dataFreeIdents: " ++ show cls ++ " not found"
  return $ Set.fromList $ catMaybes $ concat $ concat css

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
    vE <- gets valueEnv
    let preds = case qualLookupValue i vE of
          [Value _ _ _ (ForAll _ (PredType preds' ty'))] ->
            subst (matchType ty' ty idSubst) preds'
          _ -> emptyPredSet
    cs <- predFreeIdents preds
    mii <- variableFreeIdent i (foldr (TypeArrow . typeOf) ty ps)
    case mii of
      Nothing -> return Set.empty
      Just ii -> Set.insert ii . Set.union cs <$> freeIdents ps
  freeIdents (InfixFuncPattern _ (PredType _ ty) p1 i p2) = do
    mii <- variableFreeIdent i (foldr (TypeArrow . typeOf) ty [p1, p2])
    case mii of
      Nothing -> return Set.empty
      Just ii -> Set.insert ii <$> freeIdents [p1, p2]
  freeIdents (LiteralPattern _ (PredType _ ty) lit) = do
    numFreeIdent False lit ty
  freeIdents (NegativePattern _ (PredType _ ty) lit) = do
    numFreeIdent True lit ty

instance DetCheck (Expression PredType) where
  freeIdents (Variable _ (PredType _ ty) i) = do
    vE <- gets valueEnv
    let preds = case qualLookupValue i vE of
          [Value _ _ _ (ForAll _ (PredType preds' ty'))] ->
            subst (matchType ty' ty idSubst) preds'
          _ -> emptyPredSet
    cs <- predFreeIdents preds
    maybe cs (`Set.insert` cs) <$> variableFreeIdent i ty
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
  freeIdents (UnaryMinus _ e) = numFreeIdent True (Int 0) (typeOf e) `unionM` freeIdents e
  freeIdents (Literal _ (PredType _ ty) l) = numFreeIdent False l ty

instance DetCheck (InfixOp PredType) where
  freeIdents (InfixOp (PredType _ ty) i) = do
    vE <- gets valueEnv
    let preds = case qualLookupValue i vE of
          [Value _ _ _ (ForAll _ (PredType preds' ty'))] ->
            subst (matchType ty' ty idSubst) preds'
          _ -> emptyPredSet
    cs <- predFreeIdents preds
    maybe cs (`Set.insert` cs) <$> variableFreeIdent i ty
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

predFreeIdents :: PredSet -> DM (Set IdentInfo)
predFreeIdents preds = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  -- Note that an instance might have further predicates,
  -- for example the instance Header or a constrained class method.
  -- (e.g. instance Functor f => Monad (Free f))
  -- Such a pred could be at a known type constructor
  -- (e.g. when checking Monad (Free Maybe)),
  -- but we don't check it here,
  -- since the instance identifier of the original predicate (Monad (Free Maybe))
  -- will have assumed that the method used from the new pred (Functor Maybe)
  -- has its signature type if it exists.
  -- If it does not exist, it will have assumend Any as the method type.
  let go (Pred cls ty) = do
        let qcls = qualQualify mid cls
        case unapplyType True ty of
          (TypeConstructor tc, _) -> case qualLookupTypeInfo qcls tcE of
            [TypeClass _ _ meths] ->
              let mkII (ClassMethod i _ _ _ _) =
                    II qcls (zeroUniqueQual (qualQualify mid tc)) (qualifyLike qcls i { idUnique = 0})
              in Set.fromList $ map mkII meths
            _ -> internalError $ "DeterminismCheck.predFreeIdents: " ++ show cls ++ " not found"
          _ -> Set.empty
  return $ Set.unions $ map go $ Set.toList preds

variableFreeIdent :: QualIdent -> Type -> DM (Maybe IdentInfo)
variableFreeIdent qid ty = do
  vEnv <- gets valueEnv
  mid <- gets moduleIdent
  case qualLookupValueUnique mid qid vEnv of
    [Value orig mci _ (ForAll _ (PredType _ ty'))] -> case mci of
      Nothing -> return (Just (QI (zeroUniqueQual orig)))
      Just cls ->
        let qOrig = qualQualify mid orig
            qcls = qualifyLike qOrig (unqualify cls)
            sub = matchType ty' ty idSubst
            -- 0 = class type variable
            clsTy = subst sub (TypeVariable 0)
        in case unapplyType True clsTy of
            (TypeConstructor tc, _)
              -> return (Just (II qcls qtc (zeroUniqueQual qOrig { qidModule = qidModule qcls })))
                where qtc = qualQualify mid tc
            _ -> return Nothing
    [Label orig _ _] -> return (Just (QI (zeroUniqueQual orig)))
    _ -> return (Just (QI qid))

numFreeIdent :: Bool -> Literal -> Type -> DM (Set IdentInfo)
numFreeIdent _ (Char _) _ = return Set.empty
numFreeIdent _ (String _) _ = return Set.empty
numFreeIdent negated (Int _) typ = case typ of
  TypeConstructor qtc ->
      return $ Set.fromList $
        II qNumId (qualQualify preludeMIdent qtc) qFromIntId :
      [II qNumId (qualQualify preludeMIdent qtc) qNegateId | negated]
  _ -> return Set.empty
numFreeIdent negated (Float _) typ = case typ of
  TypeConstructor qtc ->
    return $ Set.fromList $
      II qNumId (qualQualify preludeMIdent qtc) qFromFloatId :
    [II qNumId (qualQualify preludeMIdent qtc) qNegateId | negated]
  _ -> return Set.empty

-- -----------------------------------------------------------------------------
-- * Checking pattern for overlap and exhaustiveness
-- -----------------------------------------------------------------------------

overlaps :: [Equation PredType] -> DM Bool
overlaps = checkOverlap . map (getPats . void)
  where
    getPats (Equation _ lhs _) = getLhsPats lhs
    getLhsPats (FunLhs _ _ ps) = ps
    getLhsPats (OpLhs _ p1 _ p2) = [p1, p2]
    getLhsPats (ApLhs _ lhs ps) = getLhsPats lhs ++ ps

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

-- -------------------------------------------------------------------
-- * Utility stuff
-- -------------------------------------------------------------------

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

zeroUniqueQual :: QualIdent -> QualIdent
zeroUniqueQual qi = qi { qidIdent = (qidIdent qi) { idUnique = 0 } }

andM :: (Foldable t, Monad m) => (a -> m Bool) -> t a -> m Bool
andM f = foldr (\a b -> f a >>= \a' -> if a' then b else return False) (return True)

unionM :: (Ord a, Monad m) => m (Set a) -> m (Set a) -> m (Set a)
unionM = liftM2 Set.union

mkArrowLike :: Type -> DetScheme
mkArrowLike = Forall [0] . mkArrowLike'
  where
    mkArrowLike' (TypeForall _ ty) = mkArrowLike' ty
    mkArrowLike' (TypeArrow ty1 ty2) =
      DetArrow (mkArrowLike' ty1) (mkArrowLike' ty2)
    mkArrowLike' _ = VarTy 0

substDetSchema :: DetScheme -> Map VarIndex DetType -> DetScheme
substDetSchema (Forall vs ty) solutions = Forall vs (substDetTy ty (foldr Map.delete solutions vs))

instantiate :: DetScheme -> DM DetType
instantiate (Forall vs ty) = do
  vs' <- replicateM (length vs) freshVar
  return (substDetTy ty (Map.fromList (zipWith (\a -> (a,) . VarTy) vs vs')))

class Constr a where
  conFields :: a -> [Ident]
  conTypes :: a -> [TypeExpr]

instance Constr NewConstrDecl where
  conFields (NewRecordDecl _ _ (f, _)) = [f]
  conFields _ = []
  conTypes (NewConstrDecl _ _ ty) = [ty]
  conTypes (NewRecordDecl _ _ (_, ty)) = [ty]

instance Constr ConstrDecl where
  conFields (RecordDecl _ _ fds) = concatMap (\(FieldDecl _ fs _) -> fs) fds
  conFields _ = []

  conTypes (ConstrDecl _ _ tys) = tys
  conTypes (ConOpDecl _ ty1 _ ty2) = [ty1, ty2]
  conTypes (RecordDecl _ _ fs) = map (\(FieldDecl _ _ ty) -> ty) fs

-- -----------------------------------------------------------------------------
-- * Error messages
-- -----------------------------------------------------------------------------

errIncorrectSig :: SpanInfo -> Ident -> String -> DetScheme -> DetScheme -> Message
errIncorrectSig p i what (Forall _ dty1) (Forall _ dty2) = spanInfoMessage p $ vcat
  [ text "Incorrect determinism signature for" <+> text what <> colon <+> pPrint i
  , text "Inferred signature:" <+> pPrint dty1
  , text "Given signature:" <+> pPrint dty2
  , text "The inferred signature is more restrictive than the given signature."
  ]

errDeterminismSignatureExt :: SpanInfo -> Message
errDeterminismSignatureExt sp = spanInfoMessage sp $ vcat
  [ text "Unexpected determinism signature"
  , text "Enable DeterminismSignatures to allow these"
  ]
