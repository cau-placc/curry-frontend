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
module Curry.Frontend.Checks.DeterminismCheck (determinismCheck, applyDetType) where

import Prelude hiding ( (<>) )
import Control.Arrow ( second )
import Control.Applicative ((<|>))
import Control.Monad ( void, zipWithM, replicateM, forM_, forM, unless, mapAndUnzipM, foldM )
import Control.Monad.State ( lift, evalStateT, modify, gets, StateT )
import Data.Equivalence.Monad ( MonadEquiv(..), EquivT, runEquivT )
import Data.List ( nub, sortOn, (\\) )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as Set

import Curry.Frontend.Base.Messages ( Message, internalError, spanInfoMessage )
import Curry.Frontend.Base.SCC ( scc )
import Curry.Frontend.Base.Types
import Curry.Frontend.Checks.TypeCheck ( checkFailablePattern )
import Curry.Base.Ident
import Curry.Base.Pretty ( Pretty(..), render, vcat, text, (<+>), (<>), colon, hsep, quotes )
import Curry.Base.SpanInfo ( SpanInfo(..), HasSpanInfo (..) )
import Curry.Syntax.Type
import Curry.Syntax.Utils ( field2Tuple, impls )
import Curry.Frontend.Env.Class ( ClassEnv, lookupClassInfo )
import Curry.Frontend.Env.Determinism
import Curry.Frontend.Env.TypeConstructor ( TCEnv, TypeInfo (..), qualLookupTypeInfo )
import Curry.Frontend.Env.Value ( qualLookupValue, qualLookupValueUnique, ValueInfo(..), ValueEnv )
import Debug.Trace
import System.IO.Unsafe (unsafePerformIO)

evalState :: StateT s IO a -> s -> a
evalState st s = unsafePerformIO (evalStateT st s)

determinismCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> DetEnv
                 -> [KnownExtension] -> Module PredType
                 -> (DetEnv, TCEnv, [Decl (PredType, DetType)], [Message])
determinismCheck mid tce ve ce de exts (Module _ _ _ _ _ _ ds) = flip evalState initState $ do
  useMap <- getUseMap mid ds
  let groups = traceShowWith pPrint $ scc (declIdents mid . fst)
                   (Set.toList . Set.unions . map (flip (Map.findWithDefault Set.empty) useMap)
                                            . declIdents mid . fst)
                   (zip ds [1..])
  ds' <- concat <$> mapM checkGroup groups
  -- traceShow (pPrint (Map.toList sigMap)) return ()
  env <- traceShowWith pPrint <$> gets detEnv
  tce' <- gets tcEnv
  msgs <- gets messages
  return (env, tce', map fst $ sortOn snd ds', msgs)
  where
    extSet = Set.fromList exts
    sigMap = sigs ds
    sigs = foldr (Map.union . sigInf) Map.empty
    sigInf (DetSig _ is dty) = Map.fromList (map (,dty) is)
    -- for class methods, we add an implicit Any signature if none is provided
    sigInf (InstanceDecl _ _ _ _ _ ds') =
      clsOrInst ds'
    sigInf (ClassDecl _ _ _ _ _ _ ds') =
      clsOrInst ds'
    sigInf _ = Map.empty
    clsOrInst ds' =
      let writtenSigs = sigs ds'
          allFunIds = map (\i -> i { idUnique = 0 }) (nub $ concatMap impls ds')
          allSigIds = Map.keys writtenSigs
      in writtenSigs `Map.union` Map.fromList (map (, AnyDetExpr NoSpanInfo) (allFunIds \\ allSigIds))
    initState = DS de (Top Map.empty) ve ce tce mid 0 [] sigMap extSet

data DS = DS { detEnv :: TopDetEnv
             , localDetEnv :: NestDetEnv
             , valueEnv :: ValueEnv
             , classEnv :: ClassEnv
             , tcEnv :: TCEnv
             , moduleIdent :: ModuleIdent
             , freshIdent :: VarIndex
             , messages :: [Message]
             , signatures :: Map Ident DetExpr
             , extensions :: Set KnownExtension
             }

type DM = StateT DS IO

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

getUseMap :: ModuleIdent -> [Decl PredType] -> DM (Map IdentInfo (Set IdentInfo))
getUseMap mid ds = do
  let go d = do
        is <- freeIdents d
        return (map (,is) (declIdents mid d))
  Map.unionsWith Set.union . map Map.fromList <$> mapM go ds

declIdents :: ModuleIdent -> Decl a -> [IdentInfo]
declIdents mid (FunctionDecl _ _ f _) =
  [QI (qualifyWith mid f)]
declIdents mid (TypeSig _ ids _) =
  map (QI . qualifyWith mid) ids
declIdents mid (ExternalDecl _ ids) =
  map (\(Var _ i) -> QI $ qualifyWith mid i) ids
declIdents _   (PatternDecl _ pat _) =
  map (QI . qualify) (patternVars pat)
declIdents mid (ClassDecl _ _ _ cls _ _ ds) =
  concatMap (map (toClassIdent (qualifyWith mid cls)) . declIdents mid) ds
declIdents mid (DataDecl _ _ _ cs _) =
  dataIdents mid (concatMap conFields cs)
declIdents mid (NewtypeDecl _ _ _ c _) =
  dataIdents mid (conFields c)
declIdents _ (FreeDecl _ vs) =
  map (\(Var _ i) -> QI $ qualify i) vs
declIdents _ _ = []

dataIdents :: ModuleIdent -> [Ident] -> [IdentInfo]
dataIdents mid = map (QI . qualifyWith mid)

-- -----------------------------------------------------------------------------
-- * Checking declaration groups and traversing the AST to generate constraints
-- -----------------------------------------------------------------------------

checkGroup :: [(Decl PredType, Integer)] -> DM [(Decl (PredType, DetType), Integer)]
checkGroup ds = do
  _ <- traceShow (pPrint ds) $ return ()
  let checkD (d, i) = fmap (second (,i)) <$> checkDecl d
  (constraintsList, ds') <- unzip <$> (mapM checkD ds >>= sequence)
  let constraints = Set.unions constraintsList
  lcl <- gets localDetEnv
  solved <- solveConstraints constraints
  let res = traceShowWith pPrint $ Map.map abstractDetScheme
                $ extractTopDetEnv
                $ mapNestDetEnv (`substDetSchema` solved) lcl
  -- By unioning with the old environment to the right, we make sure that
  -- we retain any signatures that were already present, such as user supplied ones.
  -- This ensures that we do not get follow up errors from incorrect function definitions.
  -- We take all user supplied signatures as ground truth.
  modify (\s -> s { localDetEnv = Top Map.empty
                  , detEnv = Map.union (detEnv s) res
                  , freshIdent = 0 })
  let dsUnNumbered = map fst ds'
  checkSigs dsUnNumbered res
  mapM_ (checkInstances solved) dsUnNumbered
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

checkSigs :: [Decl a] -> DetEnv -> DM ()
checkSigs ds' dE = do
  exts <- gets extensions
  let getWhat d = case d of
        FunctionDecl {} -> "function definition"
        PatternDecl {}  -> "pattern definition"
        ClassDecl {}    -> "class default method"
        _               -> "declaration"
      go mid _ what (ClassDecl _ _ _ cls _ _ ds) =
        mapM_ (go mid (toClassIdent (qualifyWith mid cls)) what) ds
      go mid to what d@FunctionDecl {} = do
        sigs <- gets signatures
        let sp = getSpanInfo d
            act (CI _ qid) dty1 = act (QI qid) dty1
            act (QI qid) dty1 = case traceShowWith (pPrint . (, "Lookup")) $ Map.lookup i sigs of
              Nothing    -> return ()
              Just dty2' -> do
                  let dty2 = toDetType dty2'
                  d1 <- traceShowWith pPrint <$> instantiate dty1
                  d2 <- traceShowWith pPrint <$> instantiate dty2
                  case d2 `moreGeneral` d1 of
                    Just _  -> return ()
                    Nothing -> addMessage (errIncorrectSig sp i what Nothing dty1 dty2)
              where i = unqualify qid
        forM_ (declIdents mid d) $ \i ->
          forM_ (Map.lookup (to i) dE) (act (to i))
      go _ _ _ (DetSig sp _ _) =
        unless (DeterminismSignatures `Set.member` exts) $
          addMessage $ errDeterminismSignatureExt sp
      go _ _ _ _ = return ()
  mid <- gets moduleIdent
  mapM_ (\d -> go mid id (getWhat d) d) ds'

checkInstances :: Map VarIndex DetType -> Decl (PredType, DetType) -> DM ()
checkInstances solved (InstanceDecl spi _ _ cls tys ds) =
  mapM_ (checkMethodImpl spi cls tys solved) ds
checkInstances _ _ = return ()

checkMethodImpl :: SpanInfo -> QualIdent -> [InstanceType] -> Map VarIndex DetType
                -> Decl (PredType, DetType) -> DM ()
checkMethodImpl spi1 cls tys subst (FunctionDecl spi2 (_, dtyInst) f _) =
  traceShow (pPrint (dtyInst, Map.toList subst)) $ do
    dEnv <- gets (traceShowWith pPrint . detEnv)
    mid <- gets moduleIdent
    let qcls = qualQualify mid cls
        fZero = f { idUnique = 0}
        qid = qualifyLike qcls fZero
        dtyCls = case Map.lookup (CI qcls qid) dEnv of
          Nothing -> internalError "checkMethodImpl: could not find class"
          Just dty -> dty
    d1 <- instantiate $ abstractDetScheme $ toDetSchema (dtyInst `substDetTy` subst)
    d2 <- instantiate dtyCls
    case d2 `moreGeneral` d1 of
      Just _  -> return ()
      Nothing -> addMessage (errIncorrectSig spi2 fZero "instance method"
                              (Just (spi1, cls, tys))
                              (Forall [] d1) dtyCls)
checkMethodImpl _ _ _ _ _ = return ()

-- Registers the types of defined variables on the outer layer, creates constraints on the inner layer.
checkDecl :: Decl PredType -> DM (DM (Set DetConstraint, Decl (PredType, DetType)))
checkDecl d@(FunctionDecl spi pty f eqs) = do
  mid <- gets moduleIdent
  act <- checkFun (declIdents mid d) eqs
  return $ do
    (cs, dty, eqs') <- act
    return (cs, FunctionDecl spi (pty, dty) f eqs')
checkDecl (PatternDecl spi p rhs) = do
  v <- freshVar
  (cs1, _, p') <- checkPat v p
  (cs2, rhs') <- scoped (checkRhsTy v rhs)
  return $ return (Set.union cs1 cs2, PatternDecl spi p' rhs')
checkDecl (ClassDecl spi li ctx cls v deps ds) = do
  acts <- mapM (checkClassDecl cls) ds
  return $ do
    (css, ds') <- unzip <$> sequence acts
    return (Set.unions css, ClassDecl spi li ctx cls v deps ds')
checkDecl (InstanceDecl spi li ctx cls tys ds) = do
  acts <- mapM (checkInstanceDecl cls) ds
  return $ do
    (css, ds') <- unzip <$> sequence acts
    return (Set.unions css, InstanceDecl spi li ctx cls tys ds')
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
  let recType = Forall [0] (DetArrow (VarTy 0) (VarTy 0))
  mapM_ (\f -> addLocalType (QI $ qualifyWith mid f) recType) $ concatMap conFields constrs
  return $
    return (Set.empty, DataDecl spi tc vs constrs deriv)
checkDecl (NewtypeDecl spi tc vs constr deriv) = do
  mid <- gets moduleIdent
  let recType = Forall [0] (DetArrow (VarTy 0) (VarTy 0))
  mapM_ (\f -> addLocalType (QI $ qualifyWith mid f) recType) $ conFields constr
  return $
    return (Set.empty, NewtypeDecl spi tc vs constr deriv)
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
      let unqualII (QI i) = QI $ qualify $ unqualify i
          unqualII (CI cls i) = CI cls $ qualify $ unqualify i
          is = map unqualII (declIdents mid d)
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

checkClassDecl :: Ident -> Decl PredType -> DM (DM (Set DetConstraint, Decl (PredType, DetType)))
checkClassDecl cls d@(FunctionDecl spi pty f eqs) = do
  mid <- gets moduleIdent
  clsEnv <- gets classEnv
  case lookupClassInfo (qualifyWith mid cls) clsEnv of
    Nothing -> internalError $ "checkClassDecl: " ++ show cls ++ " not found"
    Just (_, _, _, _) -> do
        -- Add class method `d` on global scope (happens in outer layer of checkFun)
        let is = map (toClassIdent (qualifyWith mid cls)) (declIdents mid d)
        act <- checkFun is eqs
        return $ do
          (cs, dty, eqs') <- scoped act
          return (cs, FunctionDecl spi (pty, dty) f eqs')
checkClassDecl _ d = checkDecl d

checkInstanceDecl :: QualIdent -> Decl PredType
                  -> DM (DM (Set DetConstraint, Decl (PredType, DetType)))
checkInstanceDecl cls d@(FunctionDecl spi pty f eqs) = do
  mid <- gets moduleIdent
  tcE <- gets tcEnv
  case qualLookupTypeInfo cls tcE of
    [TypeClass qcls _ cm] -> do
      let mid' = fromMaybe mid (qidModule qcls)
          is = map (toClassIdent (qualQualify mid' cls)) (declIdents mid' d)
          addSig m@(ClassMethod qid _ _ _) = case methodDetSchemeAnn m of
            Nothing  -> return ()
            Just dty -> do
              modify (\s -> s { signatures = Map.insert qid (toDetExpr dty) (signatures s) } )
      mapM_ addSig cm
      act <- checkFun is eqs
      return $ do
        (cs, dty, eqs') <- scoped act
        return (cs, FunctionDecl spi (pty, dty) f eqs')
    _ -> internalError $ "checkInstanceDecl: " ++ show cls ++ " not found"
checkInstanceDecl _ d = checkDecl d

checkFun :: [IdentInfo] -> [Equation PredType]
         -> DM (DM (Set DetConstraint, DetType, [Equation (PredType, DetType)]))
checkFun _ [] = internalError "DeterminismCheck.checkDecl: empty function"
checkFun is eqs@(e:_) = do
  let lhsArity OpLhs {} = 2
      lhsArity (FunLhs _ _ ps) = length ps
      lhsArity (ApLhs _ lhs ps) = lhsArity lhs + length ps
      arity = case e of Equation _ _ lhs _ -> lhsArity lhs
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
checkEquation args res (Equation spi mbty lhs rhs) = do
  (cs1, is, lhs') <- checkLhs args lhs
  let demands = foldr (Set.insert . EqualType res . VarTy) Set.empty is -- for all demanded variables: res ~ alpha
  (cs2, rhs') <- scoped (checkRhsTy res rhs)
  return (Set.unions [demands, cs1, cs2], Equation spi ((,VarTy res) <$> mbty) lhs' rhs')

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
checkPat v (FunctionPattern spi pty i ps) = do
  w <- freshVar
  vs <- replicateM (length ps) freshVar
  let c1 = AppliedType v w (map VarTy vs)
  let c2 = EqualType w (foldr (DetArrow . VarTy) (VarTy v) vs)
  (css, _, ps') <- unzip3 <$> zipWithM checkPat vs ps
  cs1 <- checkVar w i
  -- return True, because we assume functional pattern to be demanded
  let p' = FunctionPattern spi (pty, VarTy v) i ps'
  return (Set.insert c1 (Set.insert c2 (Set.unions (cs1:css))), True, p')
checkPat v (InfixFuncPattern spi pty p1 i p2) = do
  w <- freshVar
  v1 <- freshVar
  v2 <- freshVar
  let c1 = AppliedType v w (map VarTy [v1, v2])
  let c2 = EqualType w (foldr (DetArrow . VarTy) (VarTy v) [v1, v2])
  (cs1, _, p1') <- checkPat v1 p1
  (cs2, _, p2') <- checkPat v2 p2
  cs3 <- checkVar w i
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
  cs <- checkVar v i
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
  i <- freshVar
  let dty = foldr DetArrow (VarTy i) (replicate (arrowArity ty) (VarTy i))
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
checkExprTy v (EnumFrom spi e) = do
  (cs1, e') <- checkExprTy v e
  cs2 <- checkVar v qEnumFromId
  return (Set.union cs1 cs2, EnumFrom spi e')
checkExprTy v (EnumFromThen spi e1 e2) = do
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  cs3 <- checkVar v qEnumFromThenId
  return (Set.union (Set.union cs1 cs2) cs3, EnumFromThen spi e1' e2')
checkExprTy v (EnumFromTo spi e1 e2) = do
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  cs3 <- checkVar v qEnumFromToId
  return (Set.union (Set.union cs1 cs2) cs3, EnumFromTo spi e1' e2')
checkExprTy v (EnumFromThenTo spi e1 e2 e3) = do
  (cs1, e1') <- checkExprTy v e1
  (cs2, e2') <- checkExprTy v e2
  (cs3, e3') <- checkExprTy v e3
  cs4 <- checkVar v qEnumFromThenToId
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
  cs1 <- if any (stmtCanFail tcE) ss
    then checkVar v qFailId
    else return Set.empty
  cs2 <- checkVar v qBindId
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
  cs <- checkVar v i
  return (cs, InfixOp (ty, VarTy v) i)
checkInfixOpTy v (InfixConstr pty@(PredType _ ty) qid) = do
  i <- freshVar
  let dty = foldr DetArrow (VarTy i) (replicate (arrowArity ty) (VarTy i))
  return (Set.singleton (EqualType v dty), InfixConstr (pty, dty) qid)

checkVar :: VarIndex -> QualIdent -> DM (Set DetConstraint)
checkVar v i = do
  lcl <- gets localDetEnv
  mid <- gets moduleIdent
  ext <- gets detEnv
  vEnv <- gets valueEnv
  let ii = case qualLookupValueUnique mid i vEnv of
            [Value _ (Just (_, cls)) _ _] -> CI cls i
            _   -> QI i
  let ii' = qualifyIdentInfo mid ii
  case Map.lookup ii ext <|> Map.lookup ii' ext of
    Just ty' -> Set.singleton . EqualType v <$> instantiate ty'
    Nothing -> case lookupNestDetEnv ii lcl <|> lookupNestDetEnv ii' lcl of
      Just ty' -> Set.singleton . EqualType v <$> instantiate ty'
      Nothing
        | QI qi <- ii,
          idName (qidIdent qi) == "_"
                    -> return $ Set.singleton $ EqualType v Any
        | otherwise -> internalError $ "checkIdentInfo: " ++ render (pPrint ii) ++ " not found in \n:"
                                                          ++ render (pPrint (Map.keys ext))

-- -----------------------------------------------------------------------------
-- * Solving determinism constraints
-- -----------------------------------------------------------------------------

-- Solve by maintaining equivalence classes of variables using a union-find implementation.
-- We also keep a list that maps the highest element of each eqivalent class
-- to a non-variable determinism type if one is known.
solveConstraints :: Set DetConstraint -> DM (Map VarIndex DetType)
solveConstraints constraints = do
  lift $ traceIO ("Solving constraints: " ++ render (pPrint constraints))
  let constraintGroups = map Set.fromList $ scc defs uses $ Set.toList constraints
  runEquivT id max $ foldM solveGroup Map.empty constraintGroups

defs :: DetConstraint -> [VarIndex]
defs (EqualType v _) = [v]
defs (AppliedType v _ _) = [v]

uses :: DetConstraint -> [VarIndex]
uses (EqualType _ dty) = vars dty
uses (AppliedType _ w tys) = w : concatMap vars tys

vars :: DetType -> [VarIndex]
vars (VarTy v) = [v]
vars (DetArrow ty1 ty2) = vars ty1 ++ vars ty2
vars _ = []


solveGroup :: Map VarIndex DetType
           -> Set DetConstraint
           -> EquivT s VarIndex VarIndex DM (Map VarIndex DetType)
solveGroup substMap constraints = do
  let (applied, equal) = Set.partition isAppliedType $
                         Set.map (applySubstConstraint substMap) constraints
      isAppliedType AppliedType {} = True
      isAppliedType _ = False
  -- For AppliedType constraints, we first sort them into sccs again
  let appliedGroups = scc defs uses $ Set.toList applied
  lift $ lift $ traceIO ("Applied " ++ render (pPrint appliedGroups))
  lift $ lift $ traceIO ("Equal " ++ render (pPrint equal))
  -- If any group contains a cycle, we conservatively set all variables in that group to Any
  (newSubst, newConstraints) <- foldM transAppliedGroup (substMap, equal) appliedGroups
  lift $ lift $ traceIO ("New constraints " ++ render (pPrint newConstraints))
  -- Now, we can solve the resulting set of EqualType constraints, by sorting into sccs again
  let equalGroups = scc defs uses $ Set.toList newConstraints
  foldM solveEqualGroup newSubst equalGroups

-- We need to extend the substitution map here for all AppliedType v w tys with the
-- v variable on the left-hand side.
transAppliedGroup :: (Map VarIndex DetType, Set DetConstraint)
                  -> [DetConstraint]
                  -> EquivT s VarIndex VarIndex DM (Map VarIndex DetType, Set DetConstraint)
transAppliedGroup (substMap, otherCs) [AppliedType v w tys] =
  case Map.lookup w substMap of
    Nothing -> do
      -- emit new equality constraints that w has to be equal to the function type
      vs <- lift $ replicateM (length tys) freshVar
      let dty = foldr (DetArrow . VarTy) (VarTy v) vs
          cs = zipWith EqualType vs (map (`substDetTy` substMap) tys)
          c = EqualType w dty
      return (substMap, Set.fromList (c : cs) `Set.union` otherCs)
    Just Det -> do
      -- w is Det and thus over-applied, so v has to be Any
      return (extendSubst v Any substMap, Set.insert (EqualType v Any) otherCs)
      -- TODO: check whether w needs to be changed
    Just Any -> do
       -- w is Any, so v has to be Any as well
        return (extendSubst v Any substMap, Set.insert (EqualType v Any) otherCs)
    Just (VarTy w') -> transAppliedGroup (substMap, otherCs) [AppliedType v w' tys]
    Just arr -> do
      -- w is a function type a -> ..tys
      let (args, res) = unapplyDetType arr
      lift $ lift $ traceIO ("transAppliedGroup: function type args " ++ render (pPrint args) ++ ", tys " ++ render (pPrint tys))
      if length args < length tys
        then
          -- w is over-applied, so v has to be Any
          return (extendSubst v Any substMap, Set.insert (EqualType v Any) otherCs)
        else do
          let remaining = foldr DetArrow res $ drop (length tys) args
              c = EqualType v remaining
          let cs = Set.unions $ zipWith mkEqual args tys
          lift $ lift $ traceIO ("transAppliedGroup: generated constraints " ++ render (pPrint (c:Set.toList cs)))
          return (extendSubst v remaining substMap, Set.insert c cs `Set.union` otherCs)
  where
    mkEqual (VarTy v1) ty2 = Set.singleton (EqualType v1 ty2)
    mkEqual Det Det = Set.empty
    mkEqual Any _   = Set.empty
    mkEqual (DetArrow ty1 ty2) (DetArrow ty1' ty2') =
      Set.union (mkEqual ty1 ty1') (mkEqual ty2 ty2')
    mkEqual _ _ = error "transAppliedGroup: cannot unify function type with non-function type"
transAppliedGroup (substMap, otherCs) group = do
  let varsInGroup = concatMap defs group
  -- Set all variables in the group to Any
  let cs = Set.fromList $ map (`EqualType` Any) varsInGroup
  return (substMap, Set.union cs otherCs)

solveEqualGroup :: Map VarIndex DetType
                -> [DetConstraint]
                -> EquivT s VarIndex VarIndex DM (Map VarIndex DetType)
solveEqualGroup substMap [] = traceShowWith (pPrint . (,"solveEqGrp") . Map.toList) <$> mkSubstitution substMap
solveEqualGroup _ (AppliedType {} : _) =
  internalError "solveEqualGroup: AppliedType constraint in EqualType group"
solveEqualGroup substMap (EqualType v ty : cs) = do
  lift $ lift $ traceIO ("Solving EqualType " ++ render (pPrint (VarTy v, ty)))
  case substDetTy ty substMap of
    VarTy w
      | v == w    -> solveEqualGroup substMap cs
      | otherwise -> do
          equate v w
          d1 <- classDesc v
          d2 <- classDesc w
          let dMax = max d1 d2
          solveEqualGroup (extendSubst dMax (VarTy dMax) substMap) cs
    dty2 -> case Map.lookup v substMap of
      Nothing -> do
          solveEqualGroup (extendSubst v dty2 substMap) cs
      Just (VarTy v') -> do
          d1 <- classDesc v'
          solveEqualGroup (extendSubst d1 dty2 substMap) cs
      Just dty1 ->
        -- dty2 has to be more specific than dty1
        case moreSpecific dty2 dty1 of
          Nothing -> do
            -- Conflict, set to Any
            d1 <- classDesc v
            solveEqualGroup (extendSubst d1 Any substMap) cs
          Just cs' -> do
            -- it is more specific iff all constraints in cs' are satisfied
            let newConstraints = Set.toList cs'
            lift $ lift $ traceIO ("Adding constraints " ++ render (pPrint newConstraints))
            solveEqualGroup substMap (newConstraints ++ cs)

applySubstConstraint :: Map VarIndex DetType -> DetConstraint -> DetConstraint
applySubstConstraint substMap (EqualType v dty) =
  EqualType v (substDetTy dty substMap)
applySubstConstraint substMap (AppliedType v w tys) =
  AppliedType v w (map (`substDetTy` substMap) tys)

extendSubst :: VarIndex -> DetType -> Map VarIndex DetType -> Map VarIndex DetType
extendSubst v (VarTy w) | v == w = id
extendSubst v dty = Map.insert v dty . Map.map (`substDetTy` Map.singleton v dty)

-- For each variable that is not the maximal element in its equivalence class,
-- look up if a determinism type is known for the maximal element.
-- If it is, extend the substitution with the variable mapped to the determinism type.
-- Otherwise, extend the substitution with the variable mapped to the maximal element.
mkSubstitution :: Map VarIndex DetType
               -> EquivT s VarIndex VarIndex DM (Map VarIndex DetType)
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
  applyDetType ty2 (map (`substDetTy` Map.singleton v ty1) rest)
applyDetType (DetArrow ty1 ty2) (ty:rest) = case ty1 `moreGeneral` ty of
  Just  s -> applyDetType (substDetTy ty2 s) rest
  Nothing -> Any
applyDetType ty tys = internalError $
  "applyDetType: not enough arguments " ++ show ty ++ " @ " ++ show tys

-- The function `moreSpecific` returns `Nothing` if
-- the two types are not in the desired relation.
-- Otherwise it returns `Just cs`,
-- where `cs` are the remaining constraints that have to be satisfied.
moreSpecific :: DetType -> DetType -> Maybe (Set DetConstraint)
moreSpecific ty (VarTy v) = Just (Set.singleton (EqualType v ty))
moreSpecific (VarTy v) ty = Just (Set.singleton (EqualType v ty))
moreSpecific (DetArrow ty1 ty2) (DetArrow ty1' ty2') = do
  s1 <- ty1 `moreSpecific` ty1'
  s2 <- ty2' `moreSpecific` ty2
  return (Set.union s1 s2)
moreSpecific Det Any = Just Set.empty
moreSpecific Det Det = Just Set.empty
moreSpecific Any Any = Just Set.empty
moreSpecific _ _ = Nothing

-- The function `moreGeneral` is similar to `moreSpecific`,
-- but it checks for the opposite relation AND
-- returns a substitution mapping variables in the second type
-- to determinism types in the first type.
-- If the two types cannot be brought into the desired relation
-- by substitution, it returns `Nothing` as well.
-- This is used to check whether a function type
-- is more general than its signature annotation,
-- as well as when we already have correct determinism type information
-- in later phases.
moreGeneral :: DetType -> DetType -> Maybe (Map VarIndex DetType)
moreGeneral ty (VarTy v) = Just (Map.singleton v ty)
moreGeneral (DetArrow ty1 ty2) (DetArrow ty1' ty2') = do
  s1 <- ty1 `moreGeneral` ty1'
  s2 <- substDetTy ty2' s1 `moreGeneral` substDetTy ty2 s1
  return (s2 `Map.union` s1)
moreGeneral Det Det = Just Map.empty
moreGeneral Any Any = Just Map.empty
moreGeneral Any Det = Just Map.empty
moreGeneral _ _ = Nothing

-- -----------------------------------------------------------------------------
-- Fixing stuff after inference
-- -----------------------------------------------------------------------------

fixDecl :: Map VarIndex DetType -> Decl (PredType, DetType)
        -> DM (Decl (PredType, DetType))
fixDecl sub (FunctionDecl spi pty f eqs) = do
  eqs' <- mapM (fixEquation sub) eqs
  return (FunctionDecl spi pty f eqs')
fixDecl sub (PatternDecl spi p rhs) = do
  rhs' <- fixRhs sub rhs
  p' <- fixPat sub p
  return (PatternDecl spi p' rhs')
fixDecl sub (ClassDecl spi li ctx cls v deps ds) = do
  ds' <- mapM (fixDecl sub) ds
  return (ClassDecl spi li ctx cls v deps ds')
fixDecl sub (InstanceDecl spi li ctx cls ty ds) = do
  ds' <- mapM (fixDecl sub) ds
  return (InstanceDecl spi li ctx cls ty ds')
fixDecl sub (ExternalDecl spi vs) = do
  vs' <- mapM (fixVar sub) vs
  return (ExternalDecl spi vs')
fixDecl _ d = return d

fixEquation :: Map VarIndex DetType -> Equation (PredType, DetType)
            -> DM (Equation (PredType, DetType))
fixEquation sub (Equation spi ann lhs rhs) = do
  rhs' <- fixRhs sub rhs
  lhs' <- fixLhs sub lhs
  return (Equation spi ann lhs' rhs')

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
  ii <- variableFreeIdent i
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
  ii <- variableFreeIdent i
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
  freeIdents (ClassDecl _ _ _ _ _ _ ds) = freeIdents ds
  freeIdents (InstanceDecl _ _ _ _ _ ds) = freeIdents ds
  freeIdents (PatternDecl _ _ rhs) = freeIdents rhs
  freeIdents (FunctionDecl _ _ _ rhs) = freeIdents rhs
  freeIdents _ = return Set.empty

instance DetCheck (Rhs PredType) where
  freeIdents (SimpleRhs _ _ e ds) = freeIdents e `unionM` freeIdents ds
  freeIdents (GuardedRhs _ _ es ds) = freeIdents es `unionM` freeIdents ds

instance DetCheck (Equation PredType) where
  freeIdents (Equation _ _ lhs e) = freeIdents lhs `unionM` freeIdents e

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
  freeIdents (FunctionPattern _ _ i ps) = do
    mii <- variableFreeIdent i
    case mii of
      Nothing -> return Set.empty
      Just ii -> Set.insert ii <$> freeIdents ps
  freeIdents (InfixFuncPattern _ _ p1 i p2) = do
    mii <- variableFreeIdent i
    case mii of
      Nothing -> return Set.empty
      Just ii -> Set.insert ii <$> freeIdents [p1, p2]
  freeIdents LiteralPattern {} =
    return Set.empty
  freeIdents NegativePattern {} =
    return Set.empty

instance DetCheck (Expression PredType) where
  freeIdents (Variable _ _ i) = do
    maybe Set.empty Set.singleton <$> variableFreeIdent i
  freeIdents (Typed _ e _) = freeIdents e
  freeIdents (Apply _ e1 e2) = freeIdents e1 `unionM` freeIdents e2
  freeIdents (InfixApply _ e1 op e2) =
    freeIdents e1 `unionM` freeIdents e2 `unionM` freeIdents op
  freeIdents (Lambda _ _ e) = freeIdents e
  freeIdents (Let _ _ ds e) = freeIdents ds `unionM` freeIdents e
  freeIdents (Do _ _ ss e) = freeIdents ss `unionM` freeIdents e
  freeIdents (List _ _ es) = freeIdents es
  freeIdents Constructor {} = return Set.empty
  freeIdents (Tuple _ es) = freeIdents es
  freeIdents (ListCompr _ e qs) = freeIdents e `unionM` freeIdents qs
  freeIdents (EnumFrom _ e) = freeIdents e
  freeIdents (EnumFromThen _ e1 e2) = freeIdents e1 `unionM` freeIdents e2
  freeIdents (EnumFromTo _ e1 e2) = freeIdents e1 `unionM` freeIdents e2
  freeIdents (EnumFromThenTo _ e1 e2 e3) = freeIdents e1 `unionM` freeIdents e2 `unionM`
    freeIdents e3
  freeIdents (Paren _ e) = freeIdents e
  freeIdents (LeftSection _ e op) = freeIdents e `unionM` freeIdents op
  freeIdents (RightSection _ op e) = freeIdents op `unionM` freeIdents e
  freeIdents (Record _ _ _ fs) = freeIdents fs
  freeIdents (RecordUpdate _ e fs) = freeIdents e `unionM` freeIdents fs
  freeIdents (IfThenElse _ e1 e2 e3) =
    freeIdents e1 `unionM` freeIdents e2 `unionM` freeIdents e3
  freeIdents (Case _ _ _ e bs) = freeIdents e `unionM` freeIdents bs
  freeIdents (UnaryMinus _ e) = freeIdents e
  freeIdents Literal {} = return Set.empty

instance DetCheck (InfixOp PredType) where
  freeIdents (InfixOp _ i) =
    maybe Set.empty Set.singleton <$> variableFreeIdent i
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

variableFreeIdent :: QualIdent -> DM (Maybe IdentInfo)
variableFreeIdent qid = do
  vEnv <- gets valueEnv
  mid <- gets moduleIdent
  case qualLookupValueUnique mid qid vEnv of
    [Value orig mci _ (ForAll _ _)] -> case mci of
      Nothing -> return (Just (QI (zeroUniqueQual orig)))
      Just (_, cls) ->
        let qOrig = qualQualify mid orig
            qcls = qualifyLike qOrig (unqualify cls)
        in return (Just (CI qcls (zeroUniqueQual qOrig { qidModule = qidModule qcls })))
    [Label orig _ _] -> return (Just (QI (zeroUniqueQual orig)))
    _ -> return (Just (QI qid))

-- -----------------------------------------------------------------------------
-- * Checking pattern for overlap and exhaustiveness
-- -----------------------------------------------------------------------------

overlaps :: [Equation PredType] -> DM Bool
overlaps = checkOverlap . map (getPats . void)
  where
    getPats (Equation _ _ lhs _) = getLhsPats lhs
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

unionM :: (Ord a, Monad m) => m (Set a) -> m (Set a) -> m (Set a)
unionM = liftA2 Set.union

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

instance Constr NewConstrDecl where
  conFields (NewRecordDecl _ _ (f, _)) = [f]
  conFields _ = []

instance Constr ConstrDecl where
  conFields (RecordDecl _ _ fds) = concatMap (\(FieldDecl _ fs _) -> fs) fds
  conFields _ = []

patternVars ::  Pattern t -> [Ident]
patternVars LiteralPattern {}              = []
patternVars NegativePattern {}             = []
patternVars (VariablePattern        _ _ v) = [v]
patternVars (ConstructorPattern  _ _ _ ts) = concatMap patternVars ts
patternVars (InfixPattern     _ _ t1 _ t2) = patternVars t1 ++ patternVars t2
patternVars (ParenPattern             _ t) = patternVars t
patternVars (RecordPattern       _ _ _ fs) =
  concat [patternVars t | Field _ _ t <- fs]
patternVars (TuplePattern            _ ts) = concatMap patternVars ts
patternVars (ListPattern           _ _ ts) = concatMap patternVars ts
patternVars (AsPattern              _ v t) =
  v : patternVars t
patternVars (LazyPattern              _ t) = patternVars t
patternVars (FunctionPattern     _ _ _ ts) = nub $ concatMap patternVars ts
patternVars (InfixFuncPattern _ _ t1 _ t2) =
  nub $ patternVars t1 ++ patternVars t2

-- -----------------------------------------------------------------------------
-- * Error messages
-- -----------------------------------------------------------------------------

errIncorrectSig :: SpanInfo -> Ident -> String
                -> Maybe (SpanInfo, QualIdent, [InstanceType])
                -> DetScheme -> DetScheme -> Message
errIncorrectSig p i what mbInst (Forall _ dty1) (Forall _ dty2) =
  spanInfoMessage p $ vcat $
    (text "Incorrect determinism signature for" <+> text what <> colon <+> quotes (pPrint i)) :
    maybe [] addInstance mbInst ++
    [ text "Inferred signature:" <+> pPrint dty1
    , text "Given signature:" <+> pPrint dty2
    , text "The inferred signature is more restrictive than the given signature."
    ]
  where
    addInstance (_, cls, tys) =
      [text "In the instance declaration for" <> colon <+> pPrint cls
                                                       <+> hsep (map pPrint tys)]

errDeterminismSignatureExt :: SpanInfo -> Message
errDeterminismSignatureExt sp = spanInfoMessage sp $ vcat
  [ text "Unexpected determinism signature"
  , text "Enable DeterminismSignatures to allow these"
  ]
