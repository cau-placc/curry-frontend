{- |
    Module      :  $Header$
    Description :  Type checking Curry programs
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                                   Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2014 - 2015 Jan Tikovsky
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements the type checker of the Curry compiler. The
   type checker is invoked after the syntactic correctness of the program
   has been verified and kind checking has been applied to all type
   expressions. Local variables have been renamed already. Thus the
   compiler can maintain a flat type environment. The type checker now
   checks the correct typing of all expressions and also verifies that
   the type signatures given by the user match the inferred types. The
   type checker uses the algorithm by Damas and Milner (1982) for inferring
   the types of unannotated declarations, but allows for polymorphic
   recursion when a type annotation is present.

   The result of type checking is a (flat) top-level environment
   containing the types of all constructors, variables, and functions
   defined at the top level of a module. In addition, a type annotated
   source module is returned. Note that type annotations on the
   left hand side of a declaration hold the function or variable's
   generalized type with the type scheme's universal quantifier left
   implicit. Type annotations on the right hand side of a declaration
   hold the particular instance at which a polymorphic function or
   variable is used.
-}
{-# LANGUAGE CPP, TupleSections #-}
module Checks.TypeCheck (typeCheck) where


import Prelude hiding ((<>))

import           Control.Arrow       ( first )
import           Control.Monad.Trans ( lift )
import           Control.Monad.Extra ( allM, concatMapM, filterM, foldM
                                     , (&&^), notM, replicateM, when, unless
                                     , unlessM, mapAndUnzipM )
import qualified Control.Monad.State as S
                                     ( State, StateT, get, gets, put, modify
                                     , runState, evalStateT )
import           Data.Functor        ( (<&>) )
import           Data.Function       ( on )
import           Data.List           ( nub, nubBy, partition, sortBy, (\\) )
import qualified Data.Map            as Map ( Map, empty, elems, insert
                                            , insertWith, lookup, keysSet
                                            , partition, restrictKeys
                                            , singleton, unions )
import           Data.Maybe                 ( fromJust, fromMaybe, isJust, mapMaybe
                                            , isNothing, listToMaybe, catMaybes )
import qualified Data.Set.Extra      as Set ( Set, empty, fromList, insert
                                            , member, notMember, toList )

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Base.SpanInfo
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.Expr
import Base.Kinds
import Base.Messages (Message, spanInfoMessage, internalError)
import Base.SCC
import Base.TopEnv
import Base.TypeExpansion
import Base.Types
import Base.TypeSubst
import Base.Typing hiding (declVars)
import Base.Utils (foldr2, fst3, thd3, uncurry3, mapAccumM)

import Env.Class            as CE
import Env.Instance
import Env.TypeConstructor
import Env.Value

-- TODO: Check if the set operations on predicate sets (like union) could be
--         problematic with the 'PredIsICC' field.

-- Type checking proceeds as follows. First, the types of all data
-- constructors, field labels and class methods are entered into the
-- value environment and then a type inference for all function and
-- value definitions is performed.

typeCheck :: [KnownExtension] -> ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv
          -> InstEnv -> [Decl a] -> ([Decl PredType], ValueEnv, [Message])
typeCheck exts m tcEnv vEnv clsEnv inEnv ds = runTCM (checkDecls ds) initState
  where initState = TcState exts m tcEnv vEnv clsEnv (inEnv, Map.empty)
                            [intType, floatType] idSubst emptySigEnv 1 []

checkDecls :: [Decl a] -> TCM [Decl PredType]
checkDecls ds = do
  bindConstrs
  mapM_ checkFieldLabel (filter isTypeDecl ds) &&> bindLabels
  bindClassMethods
  mapM_ setDefaults $ filter isDefaultDecl ds
  (_, bpds') <- tcPDecls bpds
  tpds' <- mapM tcTopPDecl tpds
  theta <- getTypeSubst
  return $ map (fmap $ subst theta) $ fromPDecls $ tpds' ++ bpds'
  where (bpds, tpds) = partition (isBlockDecl . snd) $ toPDecls ds

-- The type checker makes use of a state monad in order to maintain the value
-- environment, the current substitution, and a counter which is used for
-- generating fresh type variables.

-- Additionally, an extended instance environment is used in order to handle
-- the introduction of local instances when matching a data constructor with a
-- non-empty context. This extended instance environment is composed of the
-- static top-level environment and a dynamic environment that maps each class
-- on the instances which are in scope for it. The rationale behind using this
-- representation is that it makes it easy to apply the current substitution to
-- the dynamic part of the environment. Because the dynamic instance
-- environment is also used to store explicitly annotated predicates from type
-- signatures, all entries in the dynamic instance environment carry a flag
-- that indicates whether the instance comes from a type signature or from an
-- existential quantification. True means that it comes from a quantification,
-- False means that the entry comes from a type signature

-- A so-called explicit predicate set stores the constraints mentioned in an
-- explicit type signature and those implied by them through a super class
-- relation. This set is used to prevent reporting missing instances if (and
-- only if) the programmer has explicitly constrained the respective function to
-- only be usable if such instances existed.

-- TODO: With FlexibleContexts, predicates of the explicit predicate set should
--         not be reduced during type checking.

type TCM = S.State TcState

type IsExtPred = Bool

type InstEnv' = (InstEnv, Map.Map QualIdent [([Type],IsExtPred)])

data TcState = TcState
  { extensions   :: [KnownExtension]
  , moduleIdent  :: ModuleIdent      -- read only
  , tyConsEnv    :: TCEnv
  , valueEnv     :: ValueEnv
  , classEnv     :: ClassEnv
  , instEnv      :: InstEnv'         -- instances (static and dynamic)
  , defaultTypes :: [Type]
  , typeSubst    :: TypeSubst
  , sigEnv       :: SigEnv
  , nextId       :: Int              -- automatic counter
  , errors       :: [Message]
  }

(&&>) :: TCM () -> TCM () -> TCM ()
pre &&> suf = do
  errs <- pre >> S.gets errors
  when (null errs) suf

(>>-) :: Monad m => m (a, b, c) -> (a -> b -> m a) -> m (a, c)
m >>- f = do
  (u, v, w) <- m
  u' <- f u v
  return (u', w)

(>>=-) :: TCM (a, b, d) -> (b -> TCM c) -> TCM (a, c, d)
m >>=- f = do
  (u, v, x) <- m
  w <- f v
  return (u, w, x)

runTCM :: TCM a -> TcState -> (a, ValueEnv, [Message])
runTCM tcm ts = let (a, s') = S.runState tcm ts
               in  (a, typeSubst s' `subst` valueEnv s', reverse $ errors s')

getExtensions :: TCM [KnownExtension]
getExtensions = S.gets extensions

getModuleIdent :: TCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getTyConsEnv :: TCM TCEnv
getTyConsEnv = S.gets tyConsEnv

getValueEnv :: TCM ValueEnv
getValueEnv = S.gets valueEnv

modifyValueEnv :: (ValueEnv -> ValueEnv) -> TCM ()
modifyValueEnv f = S.modify $ \s -> s { valueEnv = f $ valueEnv s }

withLocalValueEnv :: TCM a -> TCM a
withLocalValueEnv act = do
  oldEnv <- getValueEnv
  res <- act
  modifyValueEnv $ const oldEnv
  return res

getClassEnv :: TCM ClassEnv
getClassEnv = S.gets classEnv

getInstEnv :: TCM InstEnv'
getInstEnv = S.gets instEnv

modifyInstEnv :: (InstEnv' -> InstEnv') -> TCM ()
modifyInstEnv f = S.modify $ \s -> s { instEnv = f $ instEnv s }

-- taken from Leif-Erik Krueger
bindDynamicInst :: Pred -> InstEnv' -> InstEnv'
bindDynamicInst (Pred _ qcls tys) = fmap $ Map.insertWith (++) qcls [(tys,False)]

-- taken from Leif-Erik Krueger
withLocalInstEnv :: TCM a -> TCM a
withLocalInstEnv act = do
  oldEnv <- getInstEnv
  res <- act
  modifyInstEnv $ const oldEnv
  return res

getDefaultTypes :: TCM [Type]
getDefaultTypes = S.gets defaultTypes

setDefaultTypes :: [Type] -> TCM ()
setDefaultTypes tys = S.modify $ \s -> s { defaultTypes = tys }

getTypeSubst :: TCM TypeSubst
getTypeSubst = S.gets typeSubst

modifyTypeSubst :: (TypeSubst -> TypeSubst) -> TCM ()
modifyTypeSubst f = S.modify $ \s -> s { typeSubst = f $ typeSubst s }

getSigEnv :: TCM SigEnv
getSigEnv = S.gets sigEnv

setSigEnv :: SigEnv -> TCM ()
setSigEnv sigs = S.modify $ \s -> s { sigEnv = sigs }

withLocalSigEnv :: TCM a -> TCM a
withLocalSigEnv act = do
  oldSigs <- getSigEnv
  res <- act
  setSigEnv oldSigs
  return res

getNextId :: TCM Int
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

report :: Message -> TCM ()
report err = S.modify $ \s -> s { errors = err : errors s }

ok :: TCM ()
ok = return ()

-- Because the type check may mess up the order of the declarations, we
-- associate each declaration with a number. At the end of the type check,
-- we can use these numbers to restore the original declaration order.

type PDecl a = (Int, Decl a)

toPDecls :: [Decl a] -> [PDecl a]
toPDecls = zip [0 ..]

fromPDecls :: [PDecl a] -> [Decl a]
fromPDecls = map snd . sortBy (compare `on` fst)

-- During the type check we also have to convert the type of declarations
-- without annotations which is done by the function 'untyped' below.

untyped :: PDecl a -> PDecl b
untyped = fmap $ fmap $ internalError "TypeCheck.untyped"

-- Defining Data Constructors:
-- In the next step, the types of all data constructors are entered into
-- the value environment using the information entered into the type constructor
-- environment before.

bindConstrs :: TCM ()
bindConstrs = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindConstrs' m tcEnv

bindConstrs' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindConstrs' m tcEnv vEnv = foldr (bindData . snd) vEnv $ localBindings tcEnv
  where
    bindData (DataType tc k cs) vEnv' =
      let n = kindArity k in foldr (bindConstr m n (constrType' tc n)) vEnv' cs
    bindData (RenamingType tc k c) vEnv' =
      let n = kindArity k in bindNewConstr m n (constrType' tc n) c vEnv'
    bindData _ vEnv' = vEnv'

bindConstr :: ModuleIdent -> Int -> Type -> DataConstr -> ValueEnv -> ValueEnv
bindConstr m n ty (DataConstr c tys) =
  bindGlobalInfo (\qc tyScheme -> DataConstructor qc arity ls tyScheme) m c
                 (ForAll n (PredType [] (foldr TypeArrow ty tys)))
  where arity = length tys
        ls    = replicate arity anonId
bindConstr m n ty (RecordConstr c ls tys) =
  bindGlobalInfo (\qc tyScheme -> DataConstructor qc arity ls tyScheme) m c
                 (ForAll n (PredType [] (foldr TypeArrow ty tys)))
  where arity = length tys

bindNewConstr :: ModuleIdent -> Int -> Type -> DataConstr -> ValueEnv
              -> ValueEnv
bindNewConstr m n cty (DataConstr c [lty]) =
  bindGlobalInfo (`NewtypeConstructor` anonId) m c
                 (ForAll n (predType (TypeArrow lty cty)))
bindNewConstr m n cty (RecordConstr c [l] [lty]) =
  bindGlobalInfo (`NewtypeConstructor` l) m c
                 (ForAll n (predType (TypeArrow lty cty)))
bindNewConstr _ _ _ _ = internalError
  "TypeCheck.bindConstrs'.bindNewConstr: newtype with illegal constructors"

constrType' :: QualIdent -> Int -> Type
constrType' tc n =
  applyType (TypeConstructor tc) $ map TypeVariable [0 .. n - 1]

-- When a field label occurs in more than one constructor declaration of
-- a data type, the compiler ensures that the label is defined
-- consistently, i.e. both occurrences have the same type. In addition,
-- the compiler ensures that no existentially quantified type variable occurs
-- in the type of a field label because such type variables necessarily escape
-- their scope with the type of the record selection function associated with
-- the field label.

checkFieldLabel :: Decl a -> TCM ()
checkFieldLabel (DataDecl _ _ tvs cs _) = do
  ls' <- mapM (tcFieldLabel tvs) labels
  mapM_ tcFieldLabels (groupLabels ls')
  where labels = [(l, p, ty) | RecordDecl _ _ fs <- cs,
                               FieldDecl p ls ty <- fs, l <- ls]
checkFieldLabel (NewtypeDecl _ _ tvs (NewRecordDecl p _ (l, ty)) _) = do
  _ <- tcFieldLabel tvs (l, p, ty)
  ok
checkFieldLabel _ = ok

tcFieldLabel :: HasSpanInfo p => [Ident] -> (Ident, p, TypeExpr)
             -> TCM (Ident, p, Type)
tcFieldLabel tvs (l, p, ty) = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  let ForAll n (PredType _ ty') = polyType $ expandMonoType m tcEnv tvs ty
  unless (n <= length tvs) $ report $ errSkolemFieldLabel p l
  return (l, p, ty')

groupLabels :: Eq a => [(a, b, c)] -> [(a, b, [c])]
groupLabels []               = []
groupLabels ((x, y, z):xyzs) =
  (x, y, z : map thd3 xyzs') : groupLabels xyzs''
  where (xyzs', xyzs'') = partition ((x ==) . fst3) xyzs

tcFieldLabels :: HasSpanInfo p => (Ident, p, [Type]) -> TCM ()
tcFieldLabels (_, _, [])     = return ()
tcFieldLabels (l, p, ty:tys) = when (any (ty /=) tys) $ do
  m <- getModuleIdent
  report $ errIncompatibleLabelTypes p m l ty (head tys)

-- Defining Field Labels:
-- Next the types of all field labels are added to the value environment.

bindLabels :: TCM ()
bindLabels = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindLabels' m tcEnv

bindLabels' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindLabels' m tcEnv vEnv = foldr (bindData . snd) vEnv $ localBindings tcEnv
  where
    bindData (DataType tc k cs) vEnv' =
      foldr (bindLabel m n (constrType' tc n)) vEnv' $ nubBy sameLabel clabels
      where
        n = kindArity k
        labels = zip (concatMap recLabels cs) (concatMap recLabelTypes cs)
        clabels = [(l, constr l, ty) | (l, ty) <- labels]
        constr l = [qualifyLike tc (constrIdent c)
                     | c <- cs, l `elem` recLabels c]
        sameLabel (l1, _, _) (l2, _, _) = l1 == l2
    bindData (RenamingType tc k (RecordConstr c [l] [lty])) vEnv'
      = bindLabel m n (constrType' tc n) (l, [qc], lty) vEnv'
      where
        n = kindArity k
        qc = qualifyLike tc c
    bindData (RenamingType _ _ RecordConstr {}) _ =
      internalError $ "Checks.TypeCheck.bindLabels'.bindData: " ++
        "RenamingType with more than one record label"
    bindData _ vEnv' = vEnv'

bindLabel :: ModuleIdent -> Int -> Type -> (Ident, [QualIdent], Type)
          -> ValueEnv -> ValueEnv
bindLabel m n ty (l, lcs, lty) =
  bindGlobalInfo (`Label` lcs) m l
                 (ForAll n (predType (TypeArrow ty lty)))

-- Defining class methods:
-- Last, the types of all class methods are added to the value environment.

bindClassMethods :: TCM ()
bindClassMethods = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindClassMethods' m tcEnv

bindClassMethods' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindClassMethods' m tcEnv vEnv =
  foldr (bindMethods . snd) vEnv $ localBindings tcEnv
  where
    bindMethods (TypeClass cls _ ms) vEnv' =
      foldr (bindClassMethod m cls) vEnv' ms
    bindMethods _                    vEnv' =
      vEnv'

-- Since the implementations of class methods can differ in their arity,
-- we assume an arity of 0 when we enter one into the value environment.

bindClassMethod :: ModuleIdent -> QualIdent -> ClassMethod -> ValueEnv
                -> ValueEnv
bindClassMethod m cls (ClassMethod f _ ty) =
  bindGlobalInfo (\qc tySc -> Value qc (Just cls) 0 tySc) m f (typeScheme ty)

-- -----------------------------------------------------------------------------
-- Default Types
-- -----------------------------------------------------------------------------

-- Default Types:
-- The list of default types is given either by a default declaration in
-- the source code or defaults to the predefined list of numeric data types.

setDefaults :: Decl a -> TCM ()
setDefaults (DefaultDecl _ tys) = mapM toDefaultType tys >>= setDefaultTypes
  where
    toDefaultType ty =
      snd <$> (expandPoly (QualTypeExpr NoSpanInfo [] ty) >>= inst . typeScheme)
setDefaults _ = ok

-- Type Signatures:
-- The type checker collects type signatures in a flat environment.
-- The types are not expanded so that the signature is available for
-- use in the error message that is printed when the inferred type is
-- less general than the signature.

type SigEnv = Map.Map Ident QualTypeExpr

emptySigEnv :: SigEnv
emptySigEnv = Map.empty

bindTypeSig :: Ident -> QualTypeExpr -> SigEnv -> SigEnv
bindTypeSig = Map.insert

bindTypeSigs :: Decl a -> SigEnv -> SigEnv
bindTypeSigs (TypeSig _ vs ty) env = foldr (`bindTypeSig` ty) env vs
bindTypeSigs _                 env = env

lookupTypeSig :: Ident -> SigEnv -> Maybe QualTypeExpr
lookupTypeSig = Map.lookup

-- Declaration groups:
-- Before type checking a group of declarations, a dependency analysis is
-- performed and the declaration group is eventually transformed into nested
-- declaration groups which are checked separately. Within each declaration
-- group, first the value environment is extended with new bindings for all
-- variables and functions defined in the group. Next, types are inferred for
-- all declarations without an explicit type signature and the inferred types
-- are then generalized. Finally, the types of all explicitly typed declarations
-- are checked.

-- Within a group of mutually recursive declarations, all type variables that
-- appear in the types of the variables defined in the group and whose type
-- cannot be generalized must not be generalized in the other declarations of
-- that group as well.

tcDecls :: [Decl a] -> TCM (LPredList, [Decl PredType])
tcDecls = fmap (fmap fromPDecls) . tcPDecls . toPDecls

tcPDecls :: [PDecl a] -> TCM (LPredList, [PDecl PredType])
tcPDecls pds = withLocalSigEnv $ do
  let (vpds, opds) = partition (isValueDecl . snd) pds
  setSigEnv $ foldr (bindTypeSigs . snd) emptySigEnv opds
  m <- getModuleIdent
  (pls, vpdss') <-
    mapAccumM tcPDeclGroup [] $ scc (bv . snd) (qfv m . snd) vpds
  return (pls, map untyped opds ++ concat (vpdss' :: [[PDecl PredType]]))

-- TODO: This badly needs to be cleaned up due to a master thesis gone slightly wrong.
-- Especially this filterEqnType is unclear and everything is uncommented.
tcPDeclGroup :: LPredList -> [PDecl a] -> TCM (LPredList, [PDecl PredType])
tcPDeclGroup pls [(i, ExternalDecl p fs)] = do
  tys <- mapM (tcExternal . varIdent) fs
  return (pls, [(i, ExternalDecl p (zipWith (fmap . const . predType) tys fs))])
tcPDeclGroup pls [(i, FreeDecl p fvs)] = do
  vs <- mapM (tcDeclVar False) (bv fvs)
  m <- getModuleIdent
  (vs', pls') <- mapAndUnzipM addDataPred vs
  modifyValueEnv $ flip (bindVars m) vs'
  let d = FreeDecl p (map (\(v, _, ForAll _ ty) -> Var ty v) vs')
  pls'' <- improvePreds $ plUnion pls (plUnions pls')
  return (pls'', [(i, d)])
  where
    addDataPred (idt, n, ForAll ids ty1) = do
      (pls2, ty2) <- freshDataType
      let (what, idtDoc) = ("free variable", ppIdent idt)
          pls2' = map (\pr -> LPred pr (getSpanInfo idt) what idtDoc) pls2
      pls' <- unify idt what idtDoc [] (unpredType ty1) pls2' ty2
      return ((idt, n, ForAll ids ty1), pls')
tcPDeclGroup pls pds = do
  vEnv <- getValueEnv
  vss <- mapM (tcDeclVars . snd) pds
  m <- getModuleIdent
  modifyValueEnv $ flip (bindVars m) $ concat vss
  sigs <- getSigEnv
  let (impPds, expPds) = partitionPDecls sigs pds
  (pls', impPds') <- mapAccumM tcPDecl pls impPds
  plsImp <- improvePreds pls'
  substBeforeDefault <- getTypeSubst
  let substs = map (defaultTypeConstrainedDecl substBeforeDefault . snd) impPds'
  modifyTypeSubst $ \s -> foldr compose s substs
  theta <- getTypeSubst
  tvs <- concatMap (typeVars . subst theta . fst) <$>
           filterM (notM . isNonExpansive . snd . snd) impPds'
  clsEnv <- getClassEnv
  let fvs = funDepCoveragePredList clsEnv (subst theta plsImp)
              $ foldr Set.insert (fvEnv (subst theta vEnv)) tvs
      -- The predicates from the declarations that are not explicitly typed are
      -- partitioned into three groups: Local predicates, that do not contain
      -- any free type variables, are reduced and added to the types of the
      -- declarations. Mixed predicates, that contain both free and other type
      -- variables, are also added to the types of the declarations, but are not
      -- reduced. The remaining predicates are passed on together with the
      -- predicates containing free type variables from the explicitly typed
      -- declarations.
      (gpls, (mpls, lpls)) = fmap (splitPredListAny fvs) $
                                splitPredListAll fvs $ subst theta plsImp
  lpls' <- plUnion mpls <$> reducePredSet False lpls
  lpls'' <- improvePreds lpls'
  lpls3 <- foldM (uncurry . defaultPDecl fvs) lpls'' impPds'
  theta' <- getTypeSubst
  let impPds3 = map ( filterEqnType (map getPred lpls3)
                    . uncurry (fixType . gen fvs lpls3 . subst theta')) impPds'
  unlessM (elem FlexibleContexts <$> getExtensions) $
    mapM_ (reportFlexibleContextDecl m) impPds3
  modifyValueEnv $ flip (rebindVars m) (concatMap (declVars . snd) impPds3)
  impPds4 <- fixVarAnnots impPds3
  (pls'', expPds') <- mapAccumM (uncurry . tcCheckPDecl) gpls expPds
  pls3 <- improvePreds pls''
  -- We have to adapt the contexts of the annotations of equations so that it
  -- matches the corresponding entry in the value environment
  return (pls3, impPds4 ++ expPds')

partitionPDecls :: SigEnv -> [PDecl a] -> ([PDecl a], [(QualTypeExpr, PDecl a)])
partitionPDecls sigs =
  foldr (\pd -> maybe (implicit pd) (explicit pd) (typeSig $ snd pd)) ([], [])
  where implicit pd ~(impPds, expPds) = (pd : impPds, expPds)
        explicit pd qty ~(impPds, expPds) = (impPds, (qty, pd) : expPds)
        typeSig (FunctionDecl _ _ f _) = lookupTypeSig f sigs
        typeSig (PatternDecl _ (VariablePattern _ _ v) _) = lookupTypeSig v sigs
        typeSig _ = Nothing

bindVars :: ModuleIdent -> ValueEnv -> [(Ident, Int, TypeScheme)] -> ValueEnv
bindVars m = foldr $ uncurry3 $ flip (bindFun m) Nothing

rebindVars :: ModuleIdent -> ValueEnv -> [(Ident, Int, TypeScheme)] -> ValueEnv
rebindVars m = foldr $ uncurry3 $ flip (rebindFun m) Nothing

tcDeclVars :: Decl a -> TCM [(Ident, Int, TypeScheme)]
tcDeclVars (FunctionDecl _ _ f eqs) = do
  sigs <- getSigEnv
  let n = eqnArity $ head eqs
  case lookupTypeSig f sigs of
    Just qty -> do
      pty <- expandPoly qty
      return [(f, n, typeScheme pty)]
    Nothing -> do
      tys <- replicateM (n + 1) freshTypeVar
      return [(f, n, monoType $ foldr1 TypeArrow tys)]
tcDeclVars (PatternDecl _ t _) = case t of
  VariablePattern _ _ v -> return <$> tcDeclVar True v
  _ -> mapM (tcDeclVar False) (bv t)
tcDeclVars _ = internalError "TypeCheck.tcDeclVars"

tcDeclVar :: Bool -> Ident -> TCM (Ident, Int, TypeScheme)
tcDeclVar poly v = do
  sigs <- getSigEnv
  case lookupTypeSig v sigs of
    Just qty
    -- Maybe use the variables of the unpredicated type here?
      | poly || null (fv qty) -> do
        pty <- expandPoly qty
        return (v, 0, typeScheme pty)
      | otherwise -> do
        report $ errPolymorphicVar v
        lambdaVar v
    Nothing -> lambdaVar v

tcPDecl :: LPredList -> PDecl a -> TCM (LPredList, (Type, PDecl PredType))
tcPDecl pls (i, FunctionDecl p _ f eqs) = do
  vEnv <- getValueEnv
  tcFunctionPDecl i pls (varType f vEnv) p f eqs
-- taken from Leif-Erik Krueger
tcPDecl pls (i, d@(PatternDecl p (VariablePattern p' _ v) rhs)) = do
  clsEnv <- getClassEnv
  vEnv <- getValueEnv
  (exPls, ty) <- inst (varType v vEnv)
  modifyInstEnv $ flip (foldr bindDynamicInst) $ maxPredList clsEnv exPls
  (pls', rhs') <- tcRhs rhs >>-
    unify p "variable declaration" (pPrint d) pls ty
  let t' = VariablePattern p' (predType ty) v
  return (pls', (ty, (i, PatternDecl p t' rhs')))
tcPDecl pls (i, d@(PatternDecl p t rhs)) = do
  (pls', ty', t') <- tcPattern p t
  (pls'', rhs') <- tcRhs rhs >>-
    unify p "pattern declaration" (pPrint d) (plUnion pls pls') ty'
  return (pls'', (ty', (i, PatternDecl p t' rhs')))
tcPDecl _ _ = internalError "TypeCheck.tcPDecl"

-- The function 'tcFunctionPDecl' ignores the context of a function's type
-- signature. This prevents missing instance errors when the inferred type
-- of a function is less general than the declared type.

tcFunctionPDecl :: Int -> LPredList -> TypeScheme -> SpanInfo -> Ident
                -> [Equation a] -> TCM (LPredList, (Type, PDecl PredType))
tcFunctionPDecl i pls tySc@(ForAll _ pty) p f eqs = do
  -- changes taken from Leif-Erik Krueger
  clsEnv <- getClassEnv
  (exPls, ty) <- inst tySc
  modifyInstEnv $ flip (foldr bindDynamicInst) $ maxPredList clsEnv exPls
  (pls', eqs') <- tcEquations p ty pls eqs
  return (pls', (ty, (i, FunctionDecl p pty f eqs')))

tcEquations :: HasSpanInfo p => p -> Type -> LPredList -> [Equation a]
            -> TCM (LPredList, [Equation PredType])
tcEquations p ty pls eqs = do
  (pls', tys, eqs') <- tcEqns eqs
  -- TODO : improve span computation
  plss <- mapM (unify p "function definition" empty pls ty pls') tys
  let pls'' = plUnions plss
      eqs'' = map (setPredList pls'') eqs'
  return (pls'', eqs'')
 where
   setPredList preds (Equation p' (Just (PredType _ typ)) lhs rhs)
     = Equation p' (Just $ PredType (map getPred preds) typ) lhs rhs
   setPredList _     eqn = eqn

tcEqns :: [Equation a]
       -> TCM (LPredList, [Type], [Equation PredType])
tcEqns eqs = do
  plsEqs <- mapM tcEquation eqs
  let (plss, tys, eqs') = unzip3 plsEqs
      poss              = map getSpanInfo eqs
      docs              = map pPrint eqs
  pls' <- unifyList poss "equation" docs plss tys
  let eqs'' = setPredType pls' tys eqs'
  return (pls', tys, eqs'')
 where
  setPredType preds = zipWith (setPredType' preds)

  setPredType' preds ty (Equation p _ lhs rhs)
    = Equation p (Just $ PredType (map getPred preds) ty) lhs rhs

tcEquation :: Equation a -> TCM (LPredList, Type, Equation PredType)
tcEquation (Equation p _ lhs rhs) = tcEqn p lhs rhs

tcEqn :: SpanInfo -> Lhs a -> Rhs a
      -> TCM (LPredList, Type, Equation PredType)
tcEqn p lhs rhs = do
  (pls, tys, lhs', pls', ty, rhs') <- withLocalValueEnv $ do
    bindLambdaVars lhs
    (pls, tys, lhs') <- S.evalStateT (tcLhs p lhs) Set.empty
    (pls', ty, rhs') <- tcRhs rhs
    return (pls, tys, lhs', pls', ty, rhs')
  let pls'' = plUnion pls pls'
      ty' = foldr TypeArrow ty tys
  pls3 <- improvePreds pls''
  return (pls3, ty', Equation p (Just (PredType (map getPred pls'') ty')) lhs' rhs')

bindLambdaVars :: QuantExpr t => t -> TCM ()
bindLambdaVars t = do
  m <- getModuleIdent
  vs <- mapM lambdaVar (nub $ bv t)
  modifyValueEnv $ flip (bindVars m) vs

lambdaVar :: Ident -> TCM (Ident, Int, TypeScheme)
lambdaVar v = do
  ty <- freshTypeVar
  return (v, 0, monoType ty)

-- After inferring types for a group of mutually recursive declarations
-- and computing the set of its constrained type variables, the compiler
-- has to be prepared for some of the constrained type variables to not
-- appear in some of the inferred types. The type variables remaining ambiguous
-- after defaulting numeric types are reported by 'defaultPDecl'.
-- When type-checking class method implementations and explicitly typed
-- expressions, this is done by 'applyDefaultsDecl'.

defaultPDecl :: Set.Set Int -> LPredList -> Type -> PDecl a -> TCM LPredList
defaultPDecl fvs pls ty (_, FunctionDecl p _ f _) =
  applyDefaultsDecl p ("function " ++ escName f) empty fvs pls ty
defaultPDecl fvs pls ty (_, PatternDecl p (VariablePattern _ _ v) _) =
  applyDefaultsDecl p ("variable " ++ escName v) empty fvs pls ty
defaultPDecl _ pls _ (_, PatternDecl {}) = return pls
defaultPDecl _ _ _ _ = internalError "TypeCheck.defaultPDecl"

applyDefaultsDecl :: HasSpanInfo p => p -> String -> Doc -> Set.Set Int
                  -> LPredList -> Type -> TCM LPredList
applyDefaultsDecl p what doc fvs pls ty = do
  theta <- getTypeSubst
  let ty' = subst theta ty
      fvs' = foldr Set.insert fvs $ typeVars ty'
  applyDefaults p what doc fvs' pls ty'

-- After 'tcDeclGroup' has generalized the types of the implicitly
-- typed declarations of a declaration group it must update their left
-- hand side type annotations and the type environment accordingly.
-- Recall that the compiler generalizes only the types of variable and
-- function declarations.

fixType :: TypeScheme -> PDecl PredType -> PDecl PredType
fixType ~(ForAll _ pty) (i, FunctionDecl p _ f eqs) =
  (i, FunctionDecl p pty f eqs)
fixType ~(ForAll _ pty) pd@(i, PatternDecl p t rhs) = case t of
  VariablePattern spi _ v
    -> (i, PatternDecl p (VariablePattern spi pty v) rhs)
  _ -> pd
fixType _ _ = internalError "TypeCheck.fixType"

filterEqnType :: [Pred] -> PDecl PredType -> PDecl PredType
filterEqnType lpls (i, FunctionDecl p f pty eqs) =
  (i, FunctionDecl p f pty $ map (filterEqnType' lpls) eqs)
filterEqnType _    d                             = d

filterEqnType' :: [Pred] -> Equation PredType -> Equation PredType
filterEqnType' lpls (Equation p (Just (PredType _ ty)) lhs rhs) =
  Equation p (Just $ PredType lpls ty) lhs rhs
filterEqnType' _ eqn@(Equation _ Nothing _ _) = eqn

declVars :: Decl PredType -> [(Ident, Int, TypeScheme)]
declVars (FunctionDecl _ pty f eqs) =
    [(f, eqnArity $ head eqs, typeScheme pty)]
declVars (PatternDecl _ t _) = case t of
  VariablePattern _ pty v -> [(v, 0, typeScheme pty)]
  _ -> []
declVars _ = internalError "TypeCheck.declVars"

-- The function 'tcCheckPDecl' checks the type of an explicitly typed function
-- or variable declaration. After inferring a type for the declaration, the
-- inferred type is compared with the type signature. Since the inferred type
-- of an explicitly typed function or variable declaration is automatically an
-- instance of its type signature, the type signature is correct only if the
-- inferred type matches the type signature exactly except for the inferred
-- predicate set, which may contain only a subset of the declared context
-- because the context of a function's type signature is ignored in the
-- function 'tcFunctionPDecl' above.

tcCheckPDecl :: LPredList -> QualTypeExpr -> PDecl a
             -> TCM (LPredList, PDecl PredType)
tcCheckPDecl pls qty pd = withLocalInstEnv $ do
  (pls', (ty, pd')) <- tcPDecl pls pd
  plsImp <- improvePreds pls'
  theta <- getTypeSubst
  clsEnv <- getClassEnv
  fvs <- funDepCoveragePredList clsEnv (subst theta plsImp) <$> computeFvEnv
  let (gpls, lpls) = splitPredListAny fvs (subst theta plsImp)
  poly <- isNonExpansive $ snd pd
  lpls' <- reducePredSet True lpls
  lpls'' <- defaultPDecl fvs lpls' ty pd
  let ty' = subst theta ty
      tySc = if poly then gen fvs lpls'' ty' else monoType ty'
  (pls'',pd'') <- checkPDeclType qty gpls tySc pd'
  -- Because the constraints in the inferred context may be in
  -- the wrong order, we must make both contexts "equivalent"
  makeContextEquivalent pls'' (map getPred lpls'') ty' pd''

checkPDeclType :: QualTypeExpr -> LPredList -> TypeScheme -> PDecl PredType
               -> TCM (LPredList, PDecl PredType)
checkPDeclType qty pls tySc (i, FunctionDecl p _ f eqs) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral m (text "Function:" <+> ppIdent f) qty tySc
  return (pls, (i, FunctionDecl p pty f eqs))
checkPDeclType qty pls tySc (i, PatternDecl p (VariablePattern spi _ v) rhs) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral m (text "Variable:" <+> ppIdent v) qty tySc
  return (pls, (i, PatternDecl p (VariablePattern spi pty v) rhs))
checkPDeclType _ _ _ _ = internalError "TypeCheck.checkPDeclType"

checkTypeSig :: PredType -> TypeScheme -> TCM Bool
checkTypeSig (PredType sigPls sigTy) (ForAll _ (PredType pls ty)) = do
  clsEnv <- getClassEnv
  return $
    ty `eqTypes` sigTy &&
    all (`plElem` maxPredList clsEnv sigPls) pls

-- The function 'eqTypes' computes whether two types are equal modulo
-- renaming of type variables.
-- WARNING: This operation is not reflexive and expects the second type to be
-- the type signature provided by the programmer.
eqTypes :: Type -> Type -> Bool
eqTypes t1 t2 = fst (eq [] t1 t2)
 where
 -- @is@ is an AssocList of type variable indices
 eq is (TypeConstructor   qid1) (TypeConstructor   qid2) = (qid1 == qid2, is)
 eq is (TypeVariable        i1) (TypeVariable        i2)
   | i1 < 0    = (False, is)
   | otherwise = eqVar is i1 i2
 eq is (TypeConstrained ts1 i1) (TypeConstrained ts2 i2)
   = let (res1, is1) = eqs   is  ts1 ts2
         (res2, is2) = eqVar is1 i1  i2
     in  (res1 && res2, is2)
 eq is (TypeApply      ta1 tb1) (TypeApply      ta2 tb2)
   = let (res1, is1) = eq is  ta1 ta2
         (res2, is2) = eq is1 tb1 tb2
     in  (res1 && res2, is2)
 eq is (TypeArrow      tf1 tt1) (TypeArrow      tf2 tt2)
   = let (res1, is1) = eq is  tf1 tf2
         (res2, is2) = eq is1 tt1 tt2
     in  (res1 && res2, is2)
 eq is (TypeForall     is1 t1') (TypeForall     is2 t2')
   = let (res1, is') = eqs [] (map TypeVariable is1) (map TypeVariable is2)
         (res2, _  ) = eq is' t1' t2'
     in  (res1 && res2, is)
 eq is _                        _                        = (False, is)

 eqVar is i1 i2 = case lookup i1 is of
   Nothing  -> (True, (i1, i2) : is)
   Just i2' -> (i2 == i2', is)

 eqs is []        []        = (True , is)
 eqs is (t1':ts1) (t2':ts2)
    = let (res1, is1) = eq  is t1'  t2'
          (res2, is2) = eqs is1 ts1 ts2
      in  (res1 && res2, is2)
 eqs is _         _         = (False, is)


-- makes the context of the annotated type in the equation "equivalent"
-- to the context of the type annotated on the function declaration
-- and therefore also to the context of the entry in the value environment
makeContextEquivalent :: [LPred] -> [Pred] -> Type -> PDecl PredType
                      -> TCM (LPredList, PDecl PredType)
makeContextEquivalent pls pls2 ty2 (i, FunctionDecl p pty@(PredType pls1 ty1) f eqs) = do
  clsEnv <- getClassEnv
  let theta = fromMaybe (internalError "TypeCheck.checkPDeclType")
                        (matchTypeSafe ty2 ty1 idSubst)
      impPlss = map (impliedPredicatesList clsEnv) pls1
      sigPls = zip pls1 impPlss
      (pls2', _) = makeEquivalent sigPls pls2 theta
  let eqs' = map (setPredType $ PredType pls2' ty2) eqs
  return (pls, (i,FunctionDecl p pty f eqs'))
  where
    setPredType predtype (Equation spi _ lhs rhs)
      = Equation spi (Just predtype) lhs rhs
makeContextEquivalent pls _ _ d = return (pls,d)

-- first argument: all predicates from the function, with their implied predicates
-- predicates from the inferred context
-- type subst: matching computed by matching the unpredicated inferred and
-- function annotated type
makeEquivalent :: [(Pred,[Pred])] -> [Pred] -> TypeSubst -> ([Pred],TypeSubst)
makeEquivalent []         _      theta = ([], theta)
makeEquivalent (pls:plss) infPls theta =
  let (plss', theta') = makeEquivalent plss infPls theta
      matchedPreds = map (fmap fromJust) $ filter (isJust . snd)
                   $ map (\pr -> (pr, findSafeMatch pr pls theta')) infPls
  in case matchedPreds of
          []                    -> let tvs = typeVars infPls
                                       thetaInv = invSubst tvs theta'
                                   in (subst thetaInv (fst pls) : plss', theta')
          (pr,(pr', theta'')):_ -> let tvs = typeVars pr
                                       thetaInv = invSubst tvs theta''
                                   in  (subst thetaInv pr':plss', theta'')

-- finds out if a given inferred predicate matches a given predicate from the
-- function annotation or some predicate implied by the latter one
findSafeMatch :: Pred -> (Pred, [Pred]) -> TypeSubst -> Maybe (Pred, TypeSubst)
findSafeMatch pr (pr',impPls) theta = case matchPredSafe pr pr' theta of
  Nothing     -> let thetas = map (\pr'' -> (pr',) <$> matchPredSafe pr pr'' theta) impPls
                 in listToMaybe $ catMaybes thetas
  Just theta' -> Just (pr',theta')

-- Inverses a given type substitution regarding the given type variables
-- returns only variables that are matched to variables
-- TODO: This may have to be changed when implementing FlexibleContexts
invSubst :: [Int] -> TypeSubst -> TypeSubst
invSubst tvs theta =
  let subList = mapMaybe (typeVarIndex . (\ tv -> (tv, substVar theta tv))) tvs
  in foldr (\(i,j) sub -> bindVar j (TypeVariable i) sub) idSubst subList
  where
    typeVarIndex (tv,TypeVariable tv2) = Just (tv,tv2)
    typeVarIndex _                     = Nothing

-- In Curry, a non-expansive expression is either
--
-- * a literal,
-- * a variable,
-- * an application of a constructor with arity n to at most n
--   non-expansive expressions,
-- * an application of a function with arity n to at most n-1
--   non-expansive expressions, or
-- * a let expression whose body is a non-expansive expression and
--   whose local declarations are either function declarations or
--   variable declarations of the form x=e where e is a non-expansive
--   expression, or
-- * an expression whose desugared form is one of the above.
--
-- At first it may seem strange that variables are included in the list
-- above because a variable may be bound to a logical variable. However,
-- this is no problem because type variables that are present among the
-- typing assumptions of the environment enclosing a let expression
-- cannot be generalized.

class Binding a where
  isNonExpansive :: a -> TCM Bool

instance Binding a => Binding [a] where
  isNonExpansive = allM isNonExpansive

instance Binding (Decl a) where
  isNonExpansive InfixDecl {}    = return True
  isNonExpansive TypeSig {}      = return True
  isNonExpansive FunctionDecl {} = return True
  isNonExpansive ExternalDecl {} = return True
  isNonExpansive PatternDecl {}  = return False
    -- TODO: Uncomment when polymorphic let declarations are fully supported
  {-isNonExpansive (PatternDecl     _ t rhs) = case t of
    VariablePattern _ _ -> isNonExpansive rhs
    _                   -> return False-}
  isNonExpansive (FreeDecl            _ _) = return False
  isNonExpansive _                         =
    internalError "TypeCheck.isNonExpansive: declaration"

instance Binding (Rhs a) where
  isNonExpansive GuardedRhs {}        = return False
  isNonExpansive (SimpleRhs _ _ e ds) = withLocalValueEnv $ do
    m <- getModuleIdent
    tcEnv <- getTyConsEnv
    clsEnv <- getClassEnv
    sigs <- getSigEnv
    modifyValueEnv $ flip (foldr (bindDeclArity m tcEnv clsEnv sigs)) ds
    isNonExpansive e &&^ isNonExpansive ds

-- A record construction is non-expansive only if all field labels are present.

instance Binding (Expression a) where
  isNonExpansive = isNonExpansive' 0

isNonExpansive' :: Int -> Expression a -> TCM Bool
isNonExpansive' _ Literal {}              = return True
isNonExpansive' n (Variable        _ _ v)
  | v' == anonId = return False
  | isRenamed v' = do
    vEnv <- getValueEnv
    return $ n == 0 || n < varArity v vEnv
  | otherwise = do
    vEnv <- getValueEnv
    return $ n < varArity v vEnv
  where v' = unqualify v
isNonExpansive' _ Constructor {}          = return True
isNonExpansive' n (Paren             _ e) = isNonExpansive' n e
isNonExpansive' n (Typed           _ e _) = isNonExpansive' n e
isNonExpansive' _ (Record       _ _ c fs) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  fmap ((length (constrLabels m c vEnv) == length fs) &&) (isNonExpansive fs)
isNonExpansive' _ (Tuple _ es)            = isNonExpansive es
isNonExpansive' _ (List _ _ es)           = isNonExpansive es
isNonExpansive' n (Apply _ f e)           = isNonExpansive' (n + 1) f
                                              &&^ isNonExpansive e
isNonExpansive' n (InfixApply _ e1 op e2)
  = isNonExpansive' (n + 2) (infixOp op) &&^ isNonExpansive e1
                                         &&^ isNonExpansive e2
isNonExpansive' n (LeftSection _ e op)    = isNonExpansive' (n + 1) (infixOp op)
                                              &&^ isNonExpansive e
isNonExpansive' n (Lambda _ ts e)         = withLocalValueEnv $ do
  modifyValueEnv $ flip (foldr bindVarArity) (bv ts)
  fmap (((n < length ts) ||) . (all isVariablePattern ts &&))
    (isNonExpansive' (n - length ts) e)
isNonExpansive' n (Let _ _ ds e)            = withLocalValueEnv $ do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  clsEnv <- getClassEnv
  sigs <- getSigEnv
  modifyValueEnv $ flip (foldr (bindDeclArity m tcEnv clsEnv sigs)) ds
  isNonExpansive ds &&^ isNonExpansive' n e
isNonExpansive' _ _                     = return False

instance Binding a => Binding (Field a) where
  isNonExpansive (Field _ _ e) = isNonExpansive e

bindDeclArity :: ModuleIdent -> TCEnv -> ClassEnv -> SigEnv ->  Decl a
              -> ValueEnv -> ValueEnv
bindDeclArity _ _     _      _    InfixDecl {}               = id
bindDeclArity _ _     _      _    TypeSig {}                 = id
bindDeclArity _ _     _      _    (FunctionDecl   _ _ f eqs) =
  bindArity f (eqnArity $ head eqs)
bindDeclArity m tcEnv clsEnv sigs (ExternalDecl        _ fs) =
  flip (foldr $ \(Var _ f) -> bindArity f $ arrowArity $ ty f) fs
  where ty = unpredType . expandPolyType OPred m tcEnv clsEnv . fromJust .
               flip lookupTypeSig sigs
bindDeclArity _ _     _      _    (PatternDecl        _ t _) =
  flip (foldr bindVarArity) (bv t)
bindDeclArity _ _     _      _    (FreeDecl            _ vs) =
  flip (foldr bindVarArity) (bv vs)
bindDeclArity _ _     _      _    _                          =
  internalError "TypeCheck.bindDeclArity"

bindVarArity :: Ident -> ValueEnv -> ValueEnv
bindVarArity v = bindArity v 0

bindArity :: Ident -> Int -> ValueEnv -> ValueEnv
bindArity v n = bindTopEnv v (Value (qualify v) Nothing n undefined)

-- Class and instance declarations:
-- When checking method implementations in class and instance
-- declarations, the compiler must check that the inferred type matches
-- the method's declared type. This is straight forward in class
-- declarations (the only difference with respect to an overloaded
-- function with an explicit type signature is that a class method's type
-- signature is composed of its declared type signature and the context
-- from the class declaration), but a little bit more complicated for
-- instance declarations because the instance type must be substituted
-- for the type variable used in the type class declaration.
--
-- When checking inferred method types against their expected types, we have to
-- be careful because the class' n type variables are always assigned indices 0
-- to n-1 in the method types recorded in the value environment. However, in the
-- inferred type scheme returned from 'tcMethodDecl', type variables are
-- assigned indices in the order of their occurrence. In order to avoid
-- incorrectly reporting errors when the type class variables do not appear in
-- the correct order and before other type variables in a method's type,
-- 'tcInstanceMethodPDecl' normalizes the expected method type before applying
-- 'checkInstMethodType' to it. Unfortunately, this means that the compiler has
-- to add the class constraint explicitly to the type signature.

tcTopPDecl :: PDecl a -> TCM (PDecl PredType)
tcTopPDecl (i, DataDecl p tc tvs cs clss)
  = return (i, DataDecl p tc tvs cs clss)
tcTopPDecl (i, ExternalDataDecl p tc tvs)
  = return (i, ExternalDataDecl p tc tvs)
tcTopPDecl (i, NewtypeDecl p tc tvs nc clss)
  = return (i, NewtypeDecl p tc tvs nc clss)
tcTopPDecl (i, TypeDecl p tc tvs ty)
  = return (i, TypeDecl p tc tvs ty)
tcTopPDecl (i, DefaultDecl p tys)
  = return (i, DefaultDecl p tys)
tcTopPDecl (i, ClassDecl p li cx cls tvs fds ds) = withLocalSigEnv $ do
  let (vpds, opds) = partition (isValueDecl . snd) $ toPDecls ds
  setSigEnv $ foldr (bindTypeSigs . snd) emptySigEnv opds
  vpds' <- mapM (tcClassMethodPDecl (qualify cls) tvs) vpds
  return
    (i, ClassDecl p li cx cls tvs fds $ fromPDecls $ map untyped opds ++ vpds')
tcTopPDecl (i, InstanceDecl p li cx qcls tys ds) = do
  tcEnv <- getTyConsEnv
  mid <- getModuleIdent
  ptys <- expandInst mid tcEnv <$> getClassEnv <*> return cx <*> return tys
  let origCls = getOrigName mid qcls tcEnv
      clsQual = head $ filter isQualified $ reverseLookupByOrigName origCls tcEnv
      qQualCls = qualQualify (fromJust $ qidModule clsQual) qcls
  vpds' <- mapM (tcInstanceMethodPDecl qQualCls ptys) vpds
  return (i,InstanceDecl p li cx qcls tys $ fromPDecls $ map untyped opds++vpds')
  where (vpds, opds) = partition (isValueDecl . snd) $ toPDecls ds
tcTopPDecl _ = internalError "TypeCheck.tcTopDecl"

tcClassMethodPDecl :: QualIdent -> [Ident] -> PDecl a -> TCM (PDecl PredType)
tcClassMethodPDecl qcls tvs pd@(_, FunctionDecl _ _ f _) = do
  methTy <- classMethodType qualify f
  (PredType pls ty',tySc, pd') <- tcMethodPDecl qcls methTy pd
  sigs <- getSigEnv
  let QualTypeExpr spi cx ty = fromJust $ lookupTypeSig f sigs
      icc = Constraint NoSpanInfo qcls (map (VariableType NoSpanInfo) tvs)
      qty = QualTypeExpr spi (icc : cx) ty
  pd'' <- checkClassMethodType qty tySc pd'
  snd <$> makeContextEquivalent [] pls ty' pd''
tcClassMethodPDecl _ _ _ = internalError "TypeCheck.tcClassMethodPDecl"

tcInstanceMethodPDecl :: QualIdent -> PredTypes -> PDecl a
                      -> TCM (PDecl PredType)
tcInstanceMethodPDecl qcls ptys pd@(_, FunctionDecl _ _ f _) = do
  methTy <- instMethodType (qualifyLike qcls) ptys f
  (PredType pls ty, tySc, pd') <- tcMethodPDecl qcls (typeScheme methTy) pd
  pd'' <- checkInstMethodType (normalize 0 methTy) tySc pd'
  snd <$> makeContextEquivalent [] pls ty pd''
tcInstanceMethodPDecl _ _ _ = internalError "TypeCheck.tcInstanceMethodPDecl"

tcMethodPDecl :: QualIdent -> TypeScheme -> PDecl a
              -> TCM (PredType, TypeScheme, PDecl PredType)
tcMethodPDecl qcls tySc (i, FunctionDecl p _ f eqs) = withLocalValueEnv $ do
  m <- getModuleIdent
  modifyValueEnv $ bindFun m f (Just qcls) (eqnArity $ head eqs) tySc
  (pls, (ty, pd)) <- tcFunctionPDecl i [] tySc p f eqs
  let what = "implementation of method " ++ escName f
  clsEnv <- getClassEnv
  plsImp <- improvePreds pls
  theta <- getTypeSubst
  fvs <- funDepCoveragePredList clsEnv (subst theta plsImp) <$> computeFvEnv
  pls' <- reducePredSet True plsImp
  pls'' <- applyDefaultsDecl p what empty fvs pls' ty
  theta' <- getTypeSubst
  return (PredType (map getPred pls'') ty
         , gen Set.empty pls'' $ subst theta' ty, pd)
tcMethodPDecl _ _ _ = internalError "TypeCheck.tcMethodPDecl"

checkClassMethodType :: QualTypeExpr -> TypeScheme -> PDecl PredType
                     -> TCM (PDecl PredType)
checkClassMethodType qty tySc pd@(_, FunctionDecl _ _ f _) = do
  pty <- expandPolyICC ICC qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral m (text "Method:" <+> ppIdent f) qty tySc
  return pd
checkClassMethodType _ _ _ = internalError "TypeCheck.checkClassMethodType"

checkInstMethodType :: PredType -> TypeScheme -> PDecl PredType
                    -> TCM (PDecl PredType)
checkInstMethodType pty tySc pd@(_, FunctionDecl _ _ f _) = do
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $
      errMethodTypeTooSpecific f m (text "Method:" <+> ppIdent f) pty tySc
  return pd
checkInstMethodType _ _ _ = internalError "TypeCheck.checkInstMethodType"

classMethodType :: (Ident -> QualIdent) -> Ident -> TCM TypeScheme
classMethodType qual f = do
  m <- getModuleIdent
  funType False m (qual $ unRenameIdent f) <$> getValueEnv

-- Due to the sorting of the predicate set, we can simply remove the minimum
-- element as this is guaranteed to be the class constraint (see module 'Types'
-- for more information).

instMethodType :: (Ident -> QualIdent) -> PredTypes -> Ident -> TCM PredType
instMethodType qual (PredTypes pls tys) f = do
  ForAll _ (PredType pls' ty) <- classMethodType qual f
  let PredType pls'' ty' = instanceTypes tys (PredType (plDeleteMin pls') ty)
  return $ PredType (plUnion pls pls'') ty'

-- External functions:

tcExternal :: Ident -> TCM Type
tcExternal f = do
  sigs <- getSigEnv
  case lookupTypeSig f sigs of
    Nothing -> internalError "TypeCheck.tcExternal: type signature not found"
    Just (QualTypeExpr _ cx ty) -> do
      m <- getModuleIdent
      pty@(PredType _ ty') <- expandPoly $ QualTypeExpr NoSpanInfo cx ty
      modifyValueEnv $ bindFun m f Nothing (arrowArity ty') (typeScheme pty)
      return ty'

-- Patterns and Expressions:
-- Note that the type attribute associated with a constructor or infix
-- pattern is the type of the whole pattern and not the type of the
-- constructor itself. Overloaded (numeric) literals are not supported in
-- patterns.

tcLiteral :: Bool -> Literal -> TCM (PredList, Type)
tcLiteral _ (Char _) = return ([], charType)
tcLiteral poly (Int _)
  | poly      = freshNumType
  | otherwise = ([],) <$> freshConstrained numTypes
tcLiteral poly (Float _)
  | poly      = freshFractionalType
  | otherwise = ([],) <$> freshConstrained fractionalTypes
tcLiteral _    (String _) = return ([], stringType)

tcLhs :: HasSpanInfo p => p -> Lhs a -> PTCM (LPredList, [Type], Lhs PredType)
tcLhs p (FunLhs spi f ts) = do
  (plss, tys, ts') <- unzip3 <$> mapM (tcPatternHelper p False) ts
  return (plUnions plss, tys, FunLhs spi f ts')
tcLhs p (OpLhs spi t1 op t2) = do
  (pls1, ty1, t1') <- tcPatternHelper p False t1
  (pls2, ty2, t2') <- tcPatternHelper p False t2
  return (plUnion pls1 pls2, [ty1, ty2], OpLhs spi t1' op t2')
tcLhs p (ApLhs spi lhs ts) = do
  (pls, tys1, lhs') <- tcLhs p lhs
  (plss, tys2, ts') <- unzip3 <$> mapM (tcPatternHelper p False) ts
  return (plUnions (pls:plss), tys1 ++ tys2, ApLhs spi lhs' ts')

-- When computing the type of a variable in a pattern, we ignore the
-- predicate set of the variable's type (which can only be due to a type
-- signature in the same declaration group) for just the same reason as
-- in 'tcFunctionPDecl'. Infix and infix functional patterns are currently
-- checked as constructor and functional patterns, respectively, resulting
-- in slighty misleading error messages if the type check fails.

-- We also keep track of already used variables,
-- in order to add a Data constraint for non-linear patterns



tcPattern :: HasSpanInfo p => p -> Pattern a
          -> TCM (LPredList, Type, Pattern PredType)
tcPattern p = tcPatternWith Set.empty p False

-- Inside a functional pattern, a literal pattern can get a Num-constrained type,
-- Whereas a literal pattern everywhere else gets a TypeConstrained concretely to Int/Float.
-- Bool = inside FunPat
tcPatternWith :: HasSpanInfo p => Set.Set Ident -> p -> Bool -> Pattern a
              -> TCM (LPredList, Type, Pattern PredType)
tcPatternWith s p inFP pt = S.evalStateT (tcPatternHelper p inFP pt) s

type PTCM a = S.StateT (Set.Set Ident) TCM a

tcPatternHelper :: HasSpanInfo p => p -> Bool -> Pattern a
                -> PTCM (LPredList, Type, Pattern PredType)
tcPatternHelper _ inFP t@(LiteralPattern spi _ l) = do
  (pls, ty) <- lift $ tcLiteral inFP l
  let pls' = map (\pr -> LPred pr spi "literal pattern" (pPrint t)) pls
  return (pls', ty, LiteralPattern spi (predType ty) l)
tcPatternHelper _ inFP t@(NegativePattern spi _ l) = do
  (pls, ty) <- lift $ tcLiteral inFP l
  let pls' = map (\pr -> LPred pr spi "literal pattern" (pPrint t)) pls
  return (pls', ty, NegativePattern spi (predType ty) l)
tcPatternHelper _ _ t@(VariablePattern spi _ v) = do
  vEnv <- lift getValueEnv
  (pls, ty) <- lift $ inst (varType v vEnv)
  used <- S.get
  let what = "variable pattern"
  pls' <- if Set.member v used
          then return [LPred (dataPred ty) spi what (pPrint t)]
          else S.put (Set.insert v used) >> return []
  let pls'' = plUnion pls' (map (\pr -> LPred pr spi what (pPrint t)) pls)
  pls3 <- lift $ improvePreds pls''
  return (pls3, ty, VariablePattern spi (PredType (map getPred pls'') ty) v)
tcPatternHelper p inFP t@(ConstructorPattern spi _ c ts) = do
  m <- lift getModuleIdent
  vEnv <- lift getValueEnv
  (pls, (tys, ty')) <- fmap arrowUnapply <$> lift (skol (constrType m c vEnv))
  let doc = pPrintPrec 0 t
      pls' = map (\pr -> LPred pr spi "constructor pattern" doc) pls
  (pls'', ts') <- mapAccumM (uncurry . ptcPatternArg p inFP "pattern" doc) pls'
                           (zip tys ts)
  pls3 <- lift $ improvePreds pls''
  return (pls3, ty', ConstructorPattern spi (predType ty') c ts')
tcPatternHelper p inFP t@(InfixPattern spi a t1 op t2) = do
  (pls, ty, t') <- tcPatternHelper p inFP (ConstructorPattern NoSpanInfo a op [t1,t2])
  case t' of
    ConstructorPattern _ a' op' [t1', t2'] ->
      let doc = pPrint t
          pls' = map (\lpr@(LPred pr spi' what _) ->
                      if spi == spi' then LPred pr spi what doc else lpr) pls
      in return (pls', ty, InfixPattern spi a' t1' op' t2')
    _ -> internalError "TypeCheck.tcPatternHelper: Not a constructor after desugaring"
tcPatternHelper p inFP (ParenPattern spi t) = do
  (pls, ty, t') <- tcPatternHelper p inFP t
  return (pls, ty, ParenPattern spi t')
tcPatternHelper _ inFP t@(RecordPattern spi _ c fs) = do
  m <- lift getModuleIdent
  vEnv <- lift getValueEnv
  (pls, ty) <- fmap arrowBase <$> lift (skol (constrType m c vEnv))
  let (cspi, cdoc) = (getSpanInfo c, ppQIdent c)
      pls' = map (\pr -> LPred pr cspi "constructor pattern" cdoc) pls
  -- tcField does not support passing "used" variables, thus we do it by hand
  used <- S.get
  (pls'', fs') <- lift $ mapAccumM (tcField (\p -> tcPatternWith used p inFP) "pattern"
    (\t' -> pPrintPrec 0 t $-$ text "Term:" <+> pPrintPrec 0 t') ty) pls' fs
  S.put $ foldr Set.insert used $ concatMap bv fs
  pls3 <- lift $ improvePreds pls''
  return (pls3, ty, RecordPattern spi (predType ty) c fs')
tcPatternHelper p inFP (TuplePattern spi ts) = do
  (plss, tys, ts') <- unzip3 <$> mapM (tcPatternHelper p inFP) ts
  pls <- lift $ improvePreds $ plUnions plss
  return (pls, tupleType tys, TuplePattern spi ts')
tcPatternHelper p inFP t@(ListPattern spi _ ts) = do
  ty <- lift freshTypeVar
  (pls, ts') <- mapAccumM (flip (ptcPatternArg p inFP "pattern" (pPrintPrec 0 t)) ty)
                         [] ts
  pls' <- lift $ improvePreds pls
  return (pls', listType ty, ListPattern spi (predType $ listType ty) ts')
tcPatternHelper p inFP t@(AsPattern spi v t') = do
  vEnv <- lift getValueEnv
  (_, ty) <- lift $ inst (varType v vEnv)
  used <- S.get
  let (vspi, what, vdoc) = (getSpanInfo v, "variable pattern", pPrint v)
  pls <- if Set.member v used
          then return [LPred (dataPred ty) vspi what vdoc]
          else S.put (Set.insert v used) >> return []
  (pls'', t'') <- tcPatternHelper p inFP t' >>-
    (\pls' ty' -> lift $ unify p "pattern" (pPrintPrec 0 t) pls ty pls' ty')
  pls3 <- lift $ improvePreds pls''
  return (pls3, ty, AsPattern spi v t'')
tcPatternHelper p inFP (LazyPattern spi t) = do
  (pls, ty, t') <- tcPatternHelper p inFP t
  pls' <- lift $ improvePreds pls
  return (pls', ty, LazyPattern spi t')
tcPatternHelper p _ t@(FunctionPattern spi _ f ts) = do
  m <- lift getModuleIdent
  vEnv <- lift getValueEnv
  (pls, ty) <- lift $ inst (funType True m f vEnv)
  let pls' = map (\pr -> LPred pr spi "functional pattern" (pPrint t)) pls
  -- insert all
  S.modify (flip (foldr Set.insert) (bv t))
  pls'' <- lift $ improvePreds pls'
  tcFuncPattern p spi (pPrintPrec 0 t) f id pls'' ty ts
tcPatternHelper p _ t@(InfixFuncPattern spi a t1 op t2) = do
  (pls, ty, t') <- tcPatternHelper p True (FunctionPattern spi a op [t1, t2])
  case t' of
    FunctionPattern _ a' op' [t1', t2'] -> do
      let doc = pPrint t
          pls' = map (\lpr@(LPred pr spi' what _) ->
                        if spi == spi' then LPred pr spi what doc else lpr) pls
      pls'' <- lift $ improvePreds pls'
      return (pls'', ty, InfixFuncPattern spi a' t1' op' t2')
    _ -> internalError "TypeCheck.tcPatternHelper: Not a functionPattern after desugaring"

tcFuncPattern :: HasSpanInfo p => p -> SpanInfo -> Doc -> QualIdent
              -> ([Pattern PredType] -> [Pattern PredType])
              -> LPredList -> Type -> [Pattern a]
              -> PTCM (LPredList, Type, Pattern PredType)
tcFuncPattern _ spi doc f ts pls ty [] =
  let pls' = plInsert (LPred (dataPred ty) spi "functional pattern" doc) pls
  in do pls'' <- lift $ improvePreds pls'
        return (pls'', ty, FunctionPattern spi (predType ty) f (ts []))
tcFuncPattern p spi doc f ts pls ty (t':ts') = do
  (alpha, beta) <- lift $
    tcArrow p "functional pattern" (doc $-$ text "Term:" <+> pPrintPrec 0 t) ty
  (pls', t'') <- ptcPatternArg p True "functional pattern" doc pls alpha t'
  tcFuncPattern p spi doc f (ts . (t'' :)) pls' beta ts'
  where t = FunctionPattern spi (predType ty) f (ts [])

ptcPatternArg :: HasSpanInfo p => p -> Bool -> String -> Doc -> LPredList -> Type
              -> Pattern a -> PTCM (LPredList, Pattern PredType)
ptcPatternArg p inFP what doc pls ty t =
  tcPatternHelper p inFP t >>-
    (\pls' ty' -> lift $
      unify p what (doc $-$ text "Term:" <+> pPrintPrec 0 t) pls ty pls' ty')

tcPatternArg :: HasSpanInfo p => p -> String -> Doc -> LPredList -> Type
             -> Pattern a -> TCM (LPredList, Pattern PredType)
tcPatternArg p what doc pls ty t =
  tcPattern p t >>-
    unify p what (doc $-$ text "Term:" <+> pPrintPrec 0 t) pls ty

tcRhs :: Rhs a -> TCM (LPredList, Type, Rhs PredType)
tcRhs (SimpleRhs p li e ds) = do
  (pls, ds', pls', ty, e') <- withLocalValueEnv $ do
    (pls, ds') <- tcDecls ds
    (pls', ty, e') <- tcExpr e
    return (pls, ds', pls', ty, e')
  pls'' <- improvePreds $ plUnion pls pls'
  return (pls'', ty, SimpleRhs p li e' ds')
tcRhs (GuardedRhs spi li es ds) = withLocalValueEnv $ do
  (pls, ds') <- tcDecls ds
  ty <- freshTypeVar
  (pls', es') <- mapAccumM (tcCondExpr ty) pls es
  return (pls', ty, GuardedRhs spi li es' ds')

tcCondExpr :: Type -> LPredList -> CondExpr a -> TCM (LPredList, CondExpr PredType)
tcCondExpr ty pls (CondExpr p g e) = do
  (pls', g') <- tcExpr g >>- unify p "guard" (pPrintPrec 0 g) pls boolType
  (pls'', e') <- tcExpr e >>- unify p "guarded expression" (pPrintPrec 0 e) pls' ty
  return (pls'', CondExpr p g' e')

tcExpr :: Expression a -> TCM (LPredList, Type, Expression PredType)
tcExpr e@(Literal spi _ l) = do
  (pls, ty) <- tcLiteral True l
  let pls' = map (\pr -> LPred pr spi "literal" (pPrint e)) pls
  return (pls', ty, Literal spi (predType ty) l)
tcExpr e@(Variable spi _ v) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (pls, ty) <- if isAnonId (unqualify v) then freshDataType
                                         else inst (funType True m v vEnv)
  -- TODO: Maybe use a different "what" for anonymous variables
  let pls' = map (\pr -> LPred pr spi "variable" (pPrint e)) pls
  return (pls', ty, Variable spi (PredType pls ty) v)
tcExpr e@(Constructor spi _ c) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (pls, ty) <- inst (constrType m c vEnv)
  let pls' = map (\pr -> LPred pr spi "constructor" (pPrint e)) pls
  return (pls', ty, Constructor spi (predType ty) c)
tcExpr (Paren spi e) = do
  (pls, ty, e') <- tcExpr e
  return (pls, ty, Paren spi e')
tcExpr te@(Typed spi e qty) = withLocalInstEnv $ do
  let what = "explicitly typed expression"
  clsEnv <- getClassEnv
  pty <- expandPoly qty
  (pls, ty) <- inst (typeScheme pty)
  -- taken from Leif-Erik Krueger
  modifyInstEnv $ flip (foldr bindDynamicInst) $ maxPredList clsEnv pls
  let pls' = map (\pr -> LPred pr spi what (pPrint te)) pls
  (pls'', e') <- tcExpr e >>- unify spi what (pPrintPrec 0 e) [] ty
  plsImp <- improvePreds pls''
  theta <- getTypeSubst
  fvs <- funDepCoveragePredList clsEnv (subst theta plsImp) <$> computeFvEnv
  let (gpls, lpls) = splitPredListAny fvs (subst theta plsImp)
  lpls' <- reducePredSet True lpls
  lpls'' <- applyDefaultsDecl spi what (pPrint te) fvs lpls' ty
  let tySc = gen fvs lpls'' (subst theta ty)
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $
      errTypeSigTooGeneral m (text "Expression:" <+> pPrintPrec 0 e) qty tySc
  pls2 <- improvePreds $ plUnion pls' gpls
  return (pls2, ty, Typed spi e' qty)
tcExpr e@(Record spi _ c fs) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (pls, ty) <- fmap arrowBase <$> inst (constrType m c vEnv)
  let (cspi, cdoc) = (getSpanInfo c, ppQIdent c)
      pls' = map (\pr -> LPred pr cspi "constructor" cdoc) pls
  (pls'', fs') <- mapAccumM (tcField (const tcExpr) "construction"
    (\e' -> pPrintPrec 0 e $-$ text "Term:" <+> pPrintPrec 0 e') ty) pls' fs
  let missing = map (qualifyLike c) (constrLabels m c vEnv)
                  \\ map (\(Field _ qid _) -> qid) fs'
  plss <- mapM (tcMissingField spi ty) missing
  return (plUnions (pls'':plss), ty, Record spi (predType ty) c fs')
tcExpr e@(RecordUpdate spi e1 fs) = do
  (pls, ty, e1') <- tcExpr e1
  (pls', fs') <- mapAccumM (tcField (const tcExpr) "update"
    (\e' -> pPrintPrec 0 e $-$ text "Term:" <+> pPrintPrec 0 e') ty) pls fs
  pls2 <- improvePreds pls'
  return (pls2, ty, RecordUpdate spi e1' fs')
tcExpr (Tuple spi es) = do
  (plss, tys, es') <- unzip3 <$> mapM tcExpr es
  return (plUnions plss, tupleType tys, Tuple spi es')
tcExpr e@(List spi _ es) = do
  ty <- freshTypeVar
  (pls, es') <- mapAccumM (flip (tcArg spi "expression" (pPrintPrec 0 e)) ty)
                 [] es
  return (pls, listType ty, List spi (predType $ listType ty) es')
tcExpr (ListCompr spi e qs) = do
  (pls, qs', pls', ty, e') <- withLocalValueEnv $ do
    (pls, qs') <- mapAccumM (tcQual spi) [] qs
    (pls', ty, e') <- tcExpr e
    return (pls, qs', pls', ty, e')
  let pls'' = plUnion pls pls'
  pls3 <- improvePreds pls''
  return (pls3, listType ty, ListCompr spi e' qs')
tcExpr e@(EnumFrom spi e1) = do
  (pls, ty) <- freshEnumType
  let pls' = map (\pr -> LPred pr spi "arithmetic sequence" (pPrint e)) pls
  (pls'', e1') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls' ty e1
  return (pls'', listType ty, EnumFrom spi e1')
tcExpr e@(EnumFromThen spi e1 e2) = do
  (pls, ty) <- freshEnumType
  let pls' = map (\pr -> LPred pr spi "arithmetic sequence" (pPrint e)) pls
  (pls'', e1') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls' ty e1
  (pls''', e2') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls'' ty e2
  return (pls''', listType ty, EnumFromThen spi e1' e2')
tcExpr e@(EnumFromTo spi e1 e2) = do
  (pls, ty) <- freshEnumType
  let pls' = map (\pr -> LPred pr spi "arithmetic sequence" (pPrint e)) pls
  (pls'', e1') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls' ty e1
  (pls''', e2') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls'' ty e2
  return (pls''', listType ty, EnumFromTo spi e1' e2')
tcExpr e@(EnumFromThenTo spi e1 e2 e3) = do
  (pls, ty) <- freshEnumType
  let pls' = map (\pr -> LPred pr spi "arithmetic sequence" (pPrint e)) pls
  (pls2, e1') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls' ty e1
  (pls3, e2') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls2 ty e2
  (pls4, e3') <- tcArg spi "arithmetic sequence" (pPrintPrec 0 e) pls3 ty e3
  return (pls4, listType ty, EnumFromThenTo spi e1' e2' e3')
tcExpr e@(UnaryMinus spi e1) = do
  (pls, ty) <- freshNumType
  let pls' = map (\pr -> LPred pr spi "unary negation" (pPrint e)) pls
  (pls'', e1') <- tcArg spi "unary negation" (pPrintPrec 0 e) pls' ty e1
  pls3 <- improvePreds pls''
  return (pls3, ty, UnaryMinus spi e1')
tcExpr e@(Apply spi e1 e2) = do
  (pls, (alpha, beta), e1') <- tcExpr e1 >>=-
    tcArrow spi "application" (pPrintPrec 0 e $-$ text "Term:" <+> pPrintPrec 0 e1)
  (pls', e2') <- tcArg spi "application" (pPrintPrec 0 e) pls alpha e2
  pls2 <- improvePreds pls'
  return (pls2, beta, Apply spi e1' e2')
tcExpr e@(InfixApply spi e1 op e2) = do
  (pls, (alpha, beta, gamma), op') <- tcInfixOp op >>=-
    tcBinary spi "infix application" (pPrintPrec 0 e $-$ text "Operator:" <+> pPrint op)
  (pls', e1') <- tcArg spi "infix application" (pPrintPrec 0 e) pls alpha e1
  (pls'', e2') <- tcArg spi "infix application" (pPrintPrec 0 e) pls' beta e2
  pls3 <- improvePreds pls''
  return (pls3, gamma, InfixApply spi e1' op' e2')
tcExpr e@(LeftSection spi e1 op) = do
  (pls, (alpha, beta), op') <- tcInfixOp op >>=-
    tcArrow spi "left section" (pPrintPrec 0 e $-$ text "Operator:" <+> pPrint op)
  (pls', e1') <- tcArg spi "left section" (pPrintPrec 0 e) pls alpha e1
  pls2 <- improvePreds pls'
  return (pls2, beta, LeftSection spi e1' op')
tcExpr e@(RightSection spi op e1) = do
  (pls, (alpha, beta, gamma), op') <- tcInfixOp op >>=-
    tcBinary spi "right section" (pPrintPrec 0 e $-$ text "Operator:" <+> pPrint op)
  (pls', e1') <- tcArg spi "right section" (pPrintPrec 0 e) pls beta e1
  pls2 <- improvePreds pls'
  return (pls2, TypeArrow alpha gamma, RightSection spi op' e1')
tcExpr (Lambda spi ts e) = do
  (plss, tys, ts', pls, ty, e') <- withLocalValueEnv $ do
    bindLambdaVars ts
    (plss, tys, ts') <- unzip3 <$> mapM (tcPattern spi) ts
    (pls, ty, e') <- tcExpr e
    return (plss, tys, ts', pls, ty, e')
  let pls' = plUnions (pls : plss)
  pls3 <- improvePreds pls'
  return (pls3, foldr TypeArrow ty tys, Lambda spi ts' e')
tcExpr (Let spi li ds e) = do
  (pls, ds', pls', ty, e') <- withLocalValueEnv $ do
    (pls, ds') <- tcDecls ds
    (pls', ty, e') <- tcExpr e
    return (pls, ds', pls', ty, e')
  let pls'' = plUnion pls pls'
  pls3 <- improvePreds pls''
  return (pls3, ty, Let spi li ds' e')
tcExpr (Do spi li sts e) = do
  (sts', ty, pls', e') <- withLocalValueEnv $ do
    ((pls, mTy), sts') <-
      mapAccumM (uncurry (tcStmt spi)) ([], Nothing) sts
    ty <- fmap (maybe id TypeApply mTy) freshTypeVar
    (pls', e') <- tcExpr e >>- unify spi "statement" (pPrintPrec 0 e) pls ty
    return (sts', ty, pls', e')
  pls'' <- improvePreds pls'
  return (pls'', ty, Do spi li sts' e')
tcExpr e@(IfThenElse spi e1 e2 e3) = do
  (pls, e1') <- tcArg spi "expression" (pPrintPrec 0 e) [] boolType e1
  (pls', ty, e2') <- tcExpr e2
  (pls'', e3') <- tcArg spi "expression" (pPrintPrec 0 e) (plUnion pls pls') ty e3
  pls3 <- improvePreds pls''
  return (pls3, ty, IfThenElse spi e1' e2' e3')
tcExpr (Case spi li ct e as) = do
  (pls, tyLhs, e') <- tcExpr e
  tyRhs <- freshTypeVar
  (pls', as') <- mapAccumM (tcAlt tyLhs tyRhs) pls as
  pls'' <- improvePreds pls'
  return (pls'', tyRhs, Case spi li ct e' as')

tcArg :: HasSpanInfo p => p -> String -> Doc -> LPredList -> Type -> Expression a
      -> TCM (LPredList, Expression PredType)
tcArg p what doc pls ty e =
  tcExpr e >>- unify p what (doc $-$ text "Term:" <+> pPrintPrec 0 e) pls ty

tcAlt :: Type -> Type -> LPredList -> Alt a
      -> TCM (LPredList, Alt PredType)
tcAlt tyLhs tyRhs pls a@(Alt p t rhs) =
  tcAltern tyLhs p t rhs >>-
    unify p "case alternative" (pPrint a) pls tyRhs

tcAltern :: Type -> SpanInfo -> Pattern a
         -> Rhs a -> TCM (LPredList, Type, Alt PredType)
tcAltern tyLhs p t rhs = do
  (pls, t', pls', ty', rhs') <- withLocalValueEnv $ do
    bindLambdaVars t
    (pls, t') <-
      tcPatternArg p "case pattern" (pPrint (Alt p t rhs)) [] tyLhs t
    (pls', ty', rhs') <- tcRhs rhs
    return (pls, t', pls', ty', rhs')
  let pls'' = plUnion pls pls'
  pls2 <- improvePreds pls''
  return (pls2, ty', Alt p t' rhs')

tcQual :: HasSpanInfo p => p -> LPredList -> Statement a
       -> TCM (LPredList, Statement PredType)
tcQual p pls (StmtExpr spi e) = do
  (pls', e') <- tcExpr e >>- unify p "guard" (pPrintPrec 0 e) pls boolType
  return (pls', StmtExpr spi e')
tcQual _ pls (StmtDecl spi li ds) = do
  (pls', ds') <- tcDecls ds
  pls2 <- improvePreds $ plUnion pls pls'
  return (pls2, StmtDecl spi li ds')
tcQual p pls q@(StmtBind spi t e) = do
  alpha <- freshTypeVar
  (pls', e') <- tcArg p "generator" (pPrint q) pls (listType alpha) e
  bindLambdaVars t
  (pls'', t') <- tcPatternArg p "generator" (pPrint q) pls' alpha t
  pls3 <- improvePreds pls''
  return (pls3, StmtBind spi t' e')

tcStmt :: HasSpanInfo p => p -> LPredList -> Maybe Type -> Statement a
       -> TCM ((LPredList, Maybe Type), Statement PredType)
tcStmt p pls mTy (StmtExpr spi e) = do
  (pls', ty) <- maybe freshMonadType (return . (,) []) mTy
  let pls'' = map (\pr -> LPred pr spi "statement" (pPrint e)) pls'
  alpha <- freshTypeVar
  (pls''', e') <- tcExpr e >>-
    unify p "statement" (pPrintPrec 0 e) (plUnion pls pls'') (applyType ty [alpha])
  pls4 <- improvePreds pls'''
  return ((pls4, Just ty), StmtExpr spi e')
tcStmt _ pls mTy (StmtDecl spi li ds) = do
  (pls', ds') <- tcDecls ds
  pls'' <- improvePreds $ plUnion pls pls'
  return ((pls'', mTy), StmtDecl spi li ds')
tcStmt p pls mTy st@(StmtBind spi t e) = do
  failable <- checkFailableBind t
  let freshMType = if failable then freshMonadFailType else freshMonadType
  (pls', ty) <- maybe freshMType (return . (,) []) mTy
  let pls'' = map (\pr -> LPred pr spi "statement" (pPrint st)) pls'
  alpha <- freshTypeVar
  (pls3, e') <-
    tcArg p "statement" (pPrint st) (plUnion pls pls'') (applyType ty [alpha]) e
  bindLambdaVars t
  (pls4, t') <- tcPatternArg p "statement" (pPrint st) pls3 alpha t
  pls5 <- improvePreds pls4
  return ((pls5, Just ty), StmtBind spi t' e')

checkFailableBind :: Pattern a -> TCM Bool
checkFailableBind (ConstructorPattern _ _ idt ps   ) = do
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo idt tcEnv of
    [RenamingType {}    ] -> or <$> mapM checkFailableBind ps -- or [] == False
    [DataType     _ _ cs]
      | length cs == 1    -> or <$> mapM checkFailableBind ps
      | otherwise         -> return True
    _                     -> return True
checkFailableBind (InfixPattern       _ _ p1 idt p2) = do
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo idt tcEnv of
    [RenamingType {}    ] -> (||) <$> checkFailableBind p1
                                  <*> checkFailableBind p2
    [DataType     _ _ cs]
      | length cs == 1    -> (||) <$> checkFailableBind p1
                                  <*> checkFailableBind p2
      | otherwise         -> return True
    _                     -> return True
checkFailableBind (RecordPattern      _ _ idt fs   ) = do
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo idt tcEnv of
    [RenamingType {}    ] -> or <$> mapM (checkFailableBind . fieldContent) fs
    [DataType     _ _ cs]
      | length cs == 1    -> or <$> mapM (checkFailableBind . fieldContent) fs
      | otherwise         -> return True
    _                     -> return True
  where fieldContent (Field _ _ c) = c
checkFailableBind (TuplePattern       _       ps   ) =
  or <$> mapM checkFailableBind ps
checkFailableBind (AsPattern          _   _   p    ) = checkFailableBind p
checkFailableBind (ParenPattern       _       p    ) = checkFailableBind p
checkFailableBind (LazyPattern        _       _    ) = return False
checkFailableBind VariablePattern {}                 = return False
checkFailableBind _                                  = return True

tcInfixOp :: InfixOp a -> TCM (LPredList, Type, InfixOp PredType)
tcInfixOp (InfixOp _ op) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (pls, ty) <- inst (funType True m op vEnv)
  let (opspi, opdoc) = (getSpanInfo op, ppQIdent op)
      pls' = map (\pr -> LPred pr opspi "infix operator" opdoc) pls
  return (pls', ty, InfixOp (predType ty) op)
tcInfixOp (InfixConstr _ op) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (pls, ty) <- inst (constrType m op vEnv)
  let (opspi, opdoc) = (getSpanInfo op, ppQIdent op)
      pls' = map (\pr -> LPred pr opspi "infix constructor" opdoc) pls
  return (pls', ty, InfixConstr (predType ty) op)

-- The first unification in 'tcField' cannot fail; it serves only for
-- instantiating the type variables in the field label's type.

tcField :: (SpanInfo -> a b -> TCM (LPredList, Type, a PredType))
        -> String -> (a b -> Doc) -> Type -> LPredList -> Field (a b)
        -> TCM (LPredList, Field (a PredType))
tcField check what doc ty pls (Field p l x) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (pls', ty') <- inst (labelType m l vEnv)
  case ty' of
    TypeArrow ty1 ty2 -> do
      let pls'' = map (\pr -> LPred pr p "field label" (ppQIdent l)) pls'
      _ <- unify p "field label" empty [] ty [] ty1
      (pls''', x') <- check p x >>-
        unify p ("record " ++ what) (doc x) (plUnion pls pls'') ty2
      return (pls''', Field p l x')
    _ -> internalError "TypeCheck.tcField: Not an Arrow Type"

tcMissingField :: HasSpanInfo p => p -> Type -> QualIdent -> TCM LPredList
tcMissingField p ty l = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (pls, ty') <- inst (labelType m l vEnv)
  case ty' of
    TypeArrow _ ty2 ->
      let (recSpi, what, ldoc) = (getSpanInfo p, "field label", ppQIdent l)
          pls' = map (\pr -> LPred pr recSpi what ldoc) pls
          pls'' = [LPred (dataPred ty2) recSpi what ldoc]
      in unify p what empty pls' ty' pls'' (TypeArrow ty ty2)
    _ -> internalError "TypeCheck.tcMissingField: Not an Arrow Type"

-- | Checks that it's argument can be used as an arrow type @a -> b@ and returns
-- the pair @(a, b)@.
tcArrow :: HasSpanInfo p => p -> String -> Doc -> Type -> TCM (Type, Type)
tcArrow p what doc ty = do
  theta <- getTypeSubst
  unaryArrow (subst theta ty)
  where
  unaryArrow (TypeArrow ty1 ty2) = return (ty1, ty2)
  unaryArrow (TypeVariable   tv) = do
    alpha <- freshTypeVar
    beta  <- freshTypeVar
    modifyTypeSubst $ bindVar tv $ TypeArrow alpha beta
    return (alpha, beta)
  unaryArrow ty'                 = do
    m <- getModuleIdent
    report $ errNonFunctionType p what doc m ty'
    (,) <$> freshTypeVar <*> freshTypeVar

-- The function 'tcBinary' checks that its argument can be used as an arrow type
-- a -> b -> c and returns the triple (a,b,c).

tcBinary :: HasSpanInfo p => p -> String -> Doc -> Type
         -> TCM (Type, Type, Type)
tcBinary p what doc ty = tcArrow p what doc ty >>= uncurry binaryArrow
  where
  binaryArrow ty1 (TypeArrow ty2 ty3) = return (ty1, ty2, ty3)
  binaryArrow ty1 (TypeVariable   tv) = do
    beta  <- freshTypeVar
    gamma <- freshTypeVar
    modifyTypeSubst $ bindVar tv $ TypeArrow beta gamma
    return (ty1, beta, gamma)
  binaryArrow ty1 ty2                 = do
    m <- getModuleIdent
    report $ errNonBinaryOp p what doc m (TypeArrow ty1 ty2)
    (,,) ty1 <$> freshTypeVar <*> freshTypeVar

-- Unification: The unification uses Robinson's algorithm.

unify :: HasSpanInfo p => p -> String -> Doc -> LPredList -> Type -> LPredList
      -> Type -> TCM LPredList
unify p what doc pls1 ty1 pls2 ty2 = do
  theta <- getTypeSubst
  let ty1' = subst theta ty1
      ty2' = subst theta ty2
  m <- getModuleIdent
  case unifyTypes m ty1' ty2' of
    Left reason -> report $ errTypeMismatch p what doc m ty1' ty2' reason
    Right sigma -> modifyTypeSubst (compose sigma)
  return $ plUnion pls1 pls2

-- List version of unify
unifyList :: HasSpanInfo p => [p] -> String -> [Doc] -> [LPredList] -> [Type]
          -> TCM LPredList
unifyList _ _    _   []    _                        = return []
unifyList _ _    _   [pls] _                        = return pls
unifyList (p:ps) what (doc:docs) (pls1:pls2:plss) (ty1:ty2:tys) = do
  pls'  <- unifyList ps what docs (pls2:plss) (ty2:tys)
  pls'' <- unify p what doc pls1 ty1 pls2 ty2
  return $ plUnion pls' pls''
unifyList _ _ _ _ _ = internalError "TypeCheck.unifyList"

unifyTypes :: ModuleIdent -> Type -> Type -> Either Doc TypeSubst
unifyTypes _ (TypeVariable tv1) (TypeVariable tv2)
  | tv1 == tv2            = Right idSubst
  | otherwise             = Right (singleSubst tv1 (TypeVariable tv2))
unifyTypes m (TypeVariable tv) ty
  | tv `elem` typeVars ty = Left  (errRecursiveType m tv ty)
  | otherwise             = Right (singleSubst tv ty)
unifyTypes m ty (TypeVariable tv)
  | tv `elem` typeVars ty = Left  (errRecursiveType m tv ty)
  | otherwise             = Right (singleSubst tv ty)
unifyTypes _ (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2)
  | tv1  == tv2           = Right idSubst
  | tys1 == tys2          = Right (singleSubst tv1 (TypeConstrained tys2 tv2))
unifyTypes m (TypeConstrained tys tv) ty =
  foldr (choose . unifyTypes m ty) (Left (errIncompatibleTypes m ty (head tys)))
        tys
  where choose (Left _) theta' = theta'
        choose (Right theta) _ = Right (bindSubst tv ty theta)
unifyTypes m ty (TypeConstrained tys tv) =
  foldr (choose . unifyTypes m ty) (Left (errIncompatibleTypes m ty (head tys)))
        tys
  where choose (Left _) theta' = theta'
        choose (Right theta) _ = Right (bindSubst tv ty theta)
unifyTypes _ (TypeConstructor tc1) (TypeConstructor tc2)
  | tc1 == tc2 = Right idSubst
unifyTypes m (TypeApply ty11 ty12) (TypeApply ty21 ty22) =
  unifyTypeLists m [ty11, ty12] [ty21, ty22]
unifyTypes m ty1@(TypeApply _ _) (TypeArrow ty21 ty22) =
  unifyTypes m ty1 (TypeApply (TypeApply (TypeConstructor qArrowId) ty21) ty22)
unifyTypes m (TypeArrow ty11 ty12) ty2@(TypeApply _ _) =
  unifyTypes m (TypeApply (TypeApply (TypeConstructor qArrowId) ty11) ty12) ty2
unifyTypes m (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
  unifyTypeLists m [ty11, ty12] [ty21, ty22]
unifyTypes m ty1 ty2 = Left (errIncompatibleTypes m ty1 ty2)

unifyTypeLists :: ModuleIdent -> [Type] -> [Type] -> Either Doc TypeSubst
unifyTypeLists _ []           _            = Right idSubst
unifyTypeLists _ _            []           = Right idSubst
unifyTypeLists m (ty1 : tys1) (ty2 : tys2) =
  unifyTypeLists m tys1 tys2 >>= unifyTypesTheta
  where
    unifyTypesTheta theta =
      (`compose` theta) <$> unifyTypes m (subst theta ty1) (subst theta ty2)

-- After performing a unification, the resulting substitution is applied
-- to the current predicate set and the resulting predicate set is subject
-- to a reduction. This predicate set reduction retains all predicates whose
-- types are all simple variables and which are not implied by other
-- predicates in the predicate set. For all other predicates, the compiler
-- checks whether an instance exists and replaces them by applying the
-- instances' predicate set to the respective types. A minor complication
-- arises due to constrained types, which at present are used to
-- implement overloading of guard expressions and of numeric literals in
-- patterns. The set of admissible types of a constrained type may be
-- restricted by the current predicate set after the reduction and thus
-- may cause a further extension of the current type substitution.

reducePredSet :: Bool -> LPredList -> TCM LPredList
reducePredSet reportPreds pls = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  theta <- getTypeSubst
  inEnv <- fmap (fmap (map (first (subst theta)))) <$> getInstEnv
  let pls' = subst theta pls
      pm = reducePreds m inEnv pls'
      (pm1,pm2) = fmap fromJust <$> Map.partition isNothing pm
      expPls = Set.toList $ Map.keysSet pm1
      (plsDefaultable, (plsReportable, pls'')) = fmap (partition isReportable) $
        partition isDefaultable $ minPredList clsEnv (Set.toList (Map.keysSet pm2))
  theta' <- foldM (defaultTypeConstrainedPred m inEnv) idSubst plsDefaultable
  modifyTypeSubst $ compose theta'
  mapM_ report $ Map.elems $ Map.restrictKeys pm2 (Set.fromList plsReportable)
  pls3 <- improvePreds pls''
  -- If we reduce a predicate set, we have to consider that
  -- reducing a constraint can introduce new improving substitution
  -- that can influence the reduction of another constraint.
  -- Therefore, we have to reduce the predicates, improve them, and
  -- reduce and improve again until nothing changes.
  theta'' <- getTypeSubst
  let pls4 = subst theta'' pls''
  if all (`elem` pls4) pls3 && all (`elem` pls3) pls4
  then return $ expPls `plUnion` pls3
  else do pls5 <- reducePredSet reportPreds pls3
          return $ expPls `plUnion` pls5
  where

    isDefaultable :: LPred -> Bool
    isDefaultable (LPred (Pred _ qcls [TypeConstrained _ _]) _ _ _) =
      isPreludeClass qcls
    isDefaultable _ = False

    isReportable :: LPred -> Bool
    isReportable (LPred (Pred _ _ tys) _ _ _) = null (typeVars tys) ||
      reportPreds && not (all isAppliedTypeVariable tys) ||
      -- We additionally report predicates containing 'TypeConstrained's that have
      -- not already been filtered out by 'isDefaultable', as they do not satisfy
      -- the defaulting restrictions described in a comment below.

      -- We additionally report predicates containing 'TypeConstrained's that have
      -- not already been filtered out by 'isDefaultable', as they do not satisfy
      -- the defaulting restrictions described in a comment below.
      map removeTypeConstrained tys /= tys

-- taken from Leif-Erik Krueger
reducePreds :: ModuleIdent -> InstEnv' -> [LPred] -> Map.Map LPred (Maybe Message)
reducePreds m inEnv = Map.unions . map reducePred
  where
    reducePred :: LPred -> Map.Map LPred (Maybe Message)
    reducePred pr@(LPred (Pred OPred _ _) _ _ _) =
      three (Map.singleton pr . Just) (`Map.singleton` Nothing)
            (reducePreds m inEnv) (instPredList m inEnv pr)
    reducePred pr@(LPred (Pred ICC _ _) _ _ _) =
      internalError $ "TypeCheck.reducePredSet: " ++
        "tried to reduce the implicit class constraint " ++ show pr

-- TODO: With FunctionalDependencies, it might be possible to find an instance
--         even if some of the instance types are type variables.
--         Example: class C a b | a -> b
--                  instance C [a] Int
--                  Then, a constraint like C [a] b can be reduced.
-- taken from Leif-Erik Krueger
instPredList :: ModuleIdent -> InstEnv' -> LPred -> Three Message LPred LPredList
instPredList m inEnv (LPred (Pred _ qcls tys) p what doc) =
  case Map.lookup qcls $ snd inEnv of
    Just tyss | (tys,True) `elem` tyss  -> Three []
              | (tys,False) `elem` tyss -> Two lpr
    _ -> case lookupInstMatch qcls tys (fst inEnv) of
           ([], _)                -> One $ errMissingInstance m lpr
           (insts@(_ : _ : _), _) -> One $ errInstanceOverlap m lpr insts False
           (_, insts@(_ : _ : _)) -> One $ errInstanceOverlap m lpr insts True
           ([(_, ps, _, _, sigma)], _) ->
             Three $ map (\pr -> LPred pr p what doc) (subst sigma ps)
  where lpr = LPred (Pred OPred qcls (map removeTypeConstrained tys)) p what doc


data Three a b c = One a | Two b | Three c

three :: (a -> d) -> (b -> d) -> (c -> d) -> Three a b c -> d
three f _ _ (One   x) = f x
three _ g _ (Two   y) = g y
three _ _ h (Three z) = h z

-- taken from Leif-Erik Krueger
hasInstance :: ModuleIdent -> InstEnv' -> QualIdent -> [Type] -> Bool
hasInstance m inEnv qcls =
  null . reducePreds m inEnv . (:[]) . getFromPred . Pred OPred qcls

-- Predicates which have both type variables and other types as predicate types
-- (like @C Bool a@) cannot be reported in 'reducePredSet', because that would
-- lead to incorrect missing instance errors when 'reducePredSet' is called when
-- some, but not all predicate types have been inferred.
-- Therefore, to report such predicates which would only be allowed with a
-- FlexibleContexts language extension, 'reportFlexibleContextDecl' is called at
-- the end of inferring types for a declaration group.

reportFlexibleContextDecl :: ModuleIdent -> PDecl PredType -> TCM ()
reportFlexibleContextDecl m (_, FunctionDecl spi (PredType pls _) f _) =
  let flexCs = snd $ partitionPredList pls
      what   = "function declaration"
  in mapM_ (report . errFlexibleContext m spi what f) flexCs
reportFlexibleContextDecl m (_, PatternDecl _ t _) =
  reportFlexibleContextPattern m t
reportFlexibleContextDecl _ _ =
  report $ internalError "TypeCheck.reportFlexibleContextDecl"

reportFlexibleContextPattern :: ModuleIdent -> Pattern PredType -> TCM ()
reportFlexibleContextPattern _ LiteralPattern {}  = ok
reportFlexibleContextPattern _ NegativePattern {} = ok
reportFlexibleContextPattern m (VariablePattern spi (PredType pls _) v) =
  let flexCs = snd $ partitionPredList pls
      what   = "variable"
  in mapM_ (report . errFlexibleContext m spi what v) flexCs
reportFlexibleContextPattern m (ConstructorPattern _ _ _ ts) =
  mapM_ (reportFlexibleContextPattern m) ts
reportFlexibleContextPattern m (InfixPattern    _ _ t1 _ t2) =
  mapM_ (reportFlexibleContextPattern m) [t1, t2]
reportFlexibleContextPattern m (ParenPattern            _ t) =
  reportFlexibleContextPattern m t
reportFlexibleContextPattern m (RecordPattern      _ _ _ fs) =
  mapM_ (\(Field _ _ t) -> reportFlexibleContextPattern m t) fs
reportFlexibleContextPattern m (TuplePattern           _ ts) =
  mapM_ (reportFlexibleContextPattern m) ts
reportFlexibleContextPattern m (ListPattern          _ _ ts) =
  mapM_ (reportFlexibleContextPattern m) ts
reportFlexibleContextPattern m (AsPattern             _ _ t) =
  reportFlexibleContextPattern m t
reportFlexibleContextPattern m (LazyPattern             _ t) =
  reportFlexibleContextPattern m t
reportFlexibleContextPattern _ FunctionPattern {}  =
  report $ internalError "TypeCheck.reportFlexibleContextPattern"
reportFlexibleContextPattern _ InfixFuncPattern {} =
  report $ internalError "TypeCheck.reportFlexibleContextPattern"

-------------------------------------------------------------------------------
-- Improving Substitutions
-------------------------------------------------------------------------------

type TypeEqn = (Type,Type,LPred)

improvePreds :: [LPred] -> TCM [LPred]
improvePreds = improvePreds' []

improvePreds' :: [LPred] -> [LPred] -> TCM [LPred]
improvePreds' errPreds pls = do
  sigma <- getTypeSubst
  let pls'  = subst sigma pls
  tEqns <- genTypeEquations pls'
  mid <- getModuleIdent
  let (theta, errPreds') = solveTypeEqns tEqns
      errPreds'' = errPreds ++ errPreds'
  modifyTypeSubst $ compose theta
  if subst theta pls' == pls'
  then do mapM_ (report . errMissingInstance mid) (nub errPreds'')
          return (pls' \\ errPreds'')
  else improvePreds' errPreds'' (subst theta pls')


-- finding improving substitutions follows two rules
-- Given a predicate set P and a predicate C t_1 ... t_m, the following rules
-- define an improving substitution. We assume that the class declaration of
-- C looks like this:
--   class ... => C u_1 ... u_m | ... , l_1 ... l_max -> r_1 ... r_max, ...
-- Let L be the set of left indices and R the set of right indices of the
-- functional dependency
-- 1. If there is a constraint C tau_1 ... tau_m in P with t_i = tau_i
--    for all i in L, then the mgu U with U(t_j) = U(tau_j) for all j in R
--    is an improving substitution
-- 2. If there is an instance declaration of the form
--         instance ... => C tau_1 ... tau_m where
--    and there exists a substitution S with S(tau_i) = t_i for all i in L,
--    then the mgu U with U(t_j) = U(S(tau_j)) for all j in R is an
--    improving substitution.
genTypeEquations :: [LPred] -> TCM [TypeEqn]
genTypeEquations lprs = do
  tEqns1 <- firstRuleEquations lprs
  tEqns2 <- secondRuleEquations lprs
  return (tEqns1 ++ tEqns2)


firstRuleEquations :: [LPred] -> TCM [TypeEqn]
firstRuleEquations []         = return []
firstRuleEquations (lpr:lprs) = do
  let Pred _ qcls _  = getPred lpr
      lprs' = filter ((\(Pred _ qcls' _) -> qcls == qcls') . getPred) lprs
  clsEnv <- getClassEnv
  let fds = classFunDeps qcls clsEnv
      tEqns = firstRuleEquations' fds lpr lprs'
  tEqns' <- firstRuleEquations lprs
  return $ tEqns ++ tEqns'


firstRuleEquations' :: [CE.FunDep] -> LPred -> [LPred] -> [TypeEqn]
firstRuleEquations' _   _   []          = []
firstRuleEquations' fds lpr (lpr':lprs) =
  let Pred _ _ tys  = getPred lpr
      Pred _ _ tys' = getPred lpr'
      tEqns  = genTypeEqns lpr tys tys' fds
      tEqns' = firstRuleEquations' fds lpr lprs
  in tEqns ++ tEqns'

genTypeEqns :: LPred -> [Type] -> [Type] -> [CE.FunDep] -> [TypeEqn]
genTypeEqns _ _   _    []                = []
genTypeEqns lpr tys tys' ((lixs,rixs):fds) =
  let lixs' = Set.toList lixs
      rixs' = Set.toList rixs
  in if filterIndices tys lixs' == filterIndices tys' lixs'
     then zip3 (filterIndices tys rixs') (filterIndices tys' rixs') (repeat lpr)
          ++ genTypeEqns lpr tys tys' fds
     else genTypeEqns lpr tys tys' fds

secondRuleEquations :: [LPred] -> TCM [TypeEqn]
secondRuleEquations = concatMapM secondRuleEquations'

secondRuleEquations' :: LPred -> TCM [TypeEqn]
secondRuleEquations' lpr = do
  inEnv <- fst <$> getInstEnv
  clsEnv <- getClassEnv
  let Pred _ qcls tys = getPred lpr
  return $ map (\(ty,ty') -> (ty,ty',lpr))
            $ typeDepsInstEnv qcls tys clsEnv inEnv


filterIndices :: [a] -> [Int] -> [a]
filterIndices xs is = filterIndices' 0 is xs
  where
    filterIndices' _ []  _         = []
    filterIndices' _ _      []     = []
    filterIndices' i (j:js) (y:ys)
      | j == i    = y : filterIndices' (i+1) js ys
      | otherwise = filterIndices' (i+1) (j:js) ys

solveTypeEqns :: [TypeEqn] -> (TypeSubst, [LPred])
solveTypeEqns []                     = (idSubst, [])
solveTypeEqns ((ty,ty',lpr):tEqns) =
  let (theta, lprs) = solveTypeEqns tEqns
  in case unifyTypeSafe (subst theta ty) (subst theta ty') of
       Nothing     -> (theta, lpr:lprs)
       Just theta' -> (compose theta' theta, lprs)


-- taken from Leif-Erik Krueger
-- -----------------------------------------------------------------------------
-- Defaulting
-- -----------------------------------------------------------------------------

-- There are two different defaulting mechanisms in the type check, which are
-- both applied after the main part of context reduction and before generalizing
-- the inferred type to a type scheme:

-- * The type of a numeric literal appearing in a pattern is represented by a
--   'TypeConstrained', which is a special type variable annotated with a list
--   of possible types. If multiple of these types remain after the type
--   inference, they are further restricted to those that satisfy the predicates
--   on them in 'defaultTypeConstrainedPred' for those ocurring in predicates.
--   An error is reported if no such type belongs to the possible types.
--   Otherwise, or if a TypeConstrained is exclusively mentioned in the functions unconstrained type,
--   these type variables are defaulted to the first of the remaining types.
--   This happens in 'defaultTypeConstrained' used after reducing and defaulting
--   PredSets of all declarations in a declaration group.

-- * Regular type variables are defaulted in 'applyDefaults', if they are
--   ambiguous. This is explained in detail in the comment for that function.
--   In constrast to the defaulting of 'TypeConstrained's, the priority list for
--   the regular defaulting mechanism can be defined in a default declaration
--   and can therefore contain user-defined types.

-- Both defaulting mechanisms only default 'TypeConstrained's or ambiguous type
-- variables that only occur in simple predicates of the form C a, where C is
-- a Prelude class (like 'Eq', 'Num' or 'Show'). This restriction allows for a
-- simple defaulting mechanism and prevents unexpected defaulting behaviour.

-- taken from Leif-Erik Krueger
defaultTypeConstrainedPred :: ModuleIdent -> InstEnv' -> TypeSubst -> LPred
                       -> TCM TypeSubst
defaultTypeConstrainedPred m inEnv theta (LPred (Pred _ qcls tys) p what doc) =
  case subst theta tys of
    tys'@[TypeConstrained tyOpts tv] ->
      case concat (filter (hasInstance m inEnv qcls) (map (: []) tyOpts)) of
        [] -> do
          report $
            errMissingInstance m (LPred (Pred OPred qcls tys') p what doc)
          return theta
        [ty] -> return (bindSubst tv ty theta)
        tyOpts'
          | length tyOpts == length tyOpts' -> return theta
          | otherwise ->
              fmap (flip (bindSubst tv) theta) (freshConstrained tyOpts')
    tys'
      | hasInstance m inEnv qcls tys' -> return theta
      | otherwise -> do
        report $ errMissingInstance m (LPred (Pred OPred qcls tys') p what doc)
        return theta

defaultTypeConstrainedDecl :: TypeSubst -> PDecl PredType -> TypeSubst
defaultTypeConstrainedDecl s (_, FunctionDecl _ _ _ eqn) =
  foldr defaultEq idSubst eqn
  where
    defaultEq (Equation _ (Just (PredType _ ty)) _ _) = defaultTypeConstrained (subst s ty)
    defaultEq _ = id
defaultTypeConstrainedDecl _ _ = idSubst

defaultTypeConstrained :: Type -> TypeSubst -> TypeSubst
defaultTypeConstrained (TypeConstrained tyOpts tv) =
  bindSubst tv (head tyOpts)
defaultTypeConstrained (TypeApply ty1 ty2) =
  defaultTypeConstrained ty1 . defaultTypeConstrained ty2
defaultTypeConstrained (TypeArrow ty1 ty2) =
  defaultTypeConstrained ty1 . defaultTypeConstrained ty2
defaultTypeConstrained (TypeConstructor _) = id
defaultTypeConstrained (TypeVariable _) = id
defaultTypeConstrained (TypeForall _ ty) =
  defaultTypeConstrained ty

-- When a constrained type variable that is not free in the type environment
-- disappears from the current type, the type becomes ambiguous. For instance,
-- the type of the expression
--
-- let x = read "" in show x
--
-- is ambiguous assuming that 'read' and 'show' have types
--
-- read :: Read a => String -> a
-- show :: Show a => a -> String
--
-- because the compiler cannot determine which 'Read' and 'Show' instances to
-- use.
--
-- In the case of expressions with an ambiguous numeric type, i.e., a type that
-- must be an instance of 'Num' or one of its subclasses, the compiler tries to
-- resolve the ambiguity by choosing the first type from the list of default
-- types that satisfies all constraints for the ambiguous type variable. An
-- error is reported if no such type exists.

applyDefaults :: HasSpanInfo p => p -> String -> Doc -> Set.Set Int -> LPredList
              -> Type -> TCM LPredList
applyDefaults p what doc fvs pls ty = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  inEnv <- getInstEnv
  defs <- getDefaultTypes
  let pls'  = map getPred pls
      -- inspired by Leif-Erik Krueger
      theta = foldr (bindDefault m defs inEnv pls') idSubst $ nub
                [ tv | Pred _ qcls [TypeVariable tv] <- pls'
                     , tv `Set.notMember` fvs, isSimpleNumClass clsEnv qcls
                     , all (\pr -> isDefaultable pr || tv `notElem` typeVars pr) pls']
      pls'' = filter (not . null . typeVars)
                         (subst theta pls)
      ty'   = subst theta ty
      tvs'  = ambiguousTypeVars clsEnv (PredType (map getPred pls'') ty') fvs
  mapM_ (report . errAmbiguousTypeVariable m p what doc pls'' ty') tvs'
  modifyTypeSubst $ compose theta
  return pls''
 where
   -- taken from Leif-Erik Krueger
  isDefaultable :: Pred -> Bool
  isDefaultable (Pred _ qcls [TypeVariable _]) = isPreludeClass qcls
  isDefaultable _                              = False



bindDefault :: ModuleIdent -> [Type] -> InstEnv' -> PredList -> Int -> TypeSubst -> TypeSubst
bindDefault m defs inEnv pls tv =
  case foldr (defaultType m inEnv tv) defs pls of
    [] -> id
    ty:_ -> bindSubst tv ty

-- TODO: The second TODO comment of 'reportMissingInstance' applies here too.
defaultType :: ModuleIdent -> InstEnv' -> Int -> Pred -> [Type] -> [Type]
defaultType m inEnv tv (Pred _ qcls [TypeVariable tv'])
  | tv == tv' = concat . filter (hasInstance m inEnv qcls) . map (: [])
  | otherwise = id
defaultType _ _ _ _ = id

-- TODO: Check if a more generalized version of this working with
--         multi-parameter type classes would be useful.
--       In the other direction, restricting this to Prelude subclasses of 'Num'
--         might be useful.
-- taken from Leif-Erik Krueger
isSimpleNumClass :: ClassEnv -> QualIdent -> Bool
isSimpleNumClass =
  (plElem (Pred OPred qNumId [TypeVariable 0]) .) . flip allSuperClasses

-- taken from Leif-Erik Krueger
isPreludeClass :: QualIdent -> Bool
isPreludeClass qcls = qcls `elem`
  [ qEqId, qOrdId, qEnumId, qBoundedId, qReadId, qShowId, qNumId, qFractionalId
  , qRealId, qIntegralId, qRealFracId, qFloatingId, qMonoidId, qFunctorId
  , qApplicativeId, qAlternativeId, qMonadId, qMonadFailId, qDataId ]

-- ----------------------------------------------------------------------------
-- Adapt type annotations of equations to the corresponding type scheme from
-- the value environment
-- ----------------------------------------------------------------------------

fixVarAnnots :: [PDecl PredType] -> TCM [PDecl PredType]
fixVarAnnots = mapM (\(i,d) -> fixVarAnnotsDecl [] d <&> (i,))

fixVarAnnotsDecl :: [Pred] -> Decl PredType -> TCM (Decl PredType)
fixVarAnnotsDecl pls (FunctionDecl spi pty f eqs) = do
  eqs' <- mapM (fixVarAnnotsEquation pls) eqs
  return $ FunctionDecl spi pty f eqs'
fixVarAnnotsDecl pls (ClassDecl spi li cx cls tvs fdps ms)
  = ClassDecl spi li cx cls tvs fdps <$> mapM (fixVarAnnotsDecl pls) ms
fixVarAnnotsDecl pls (InstanceDecl spi li cx qcls insty ds)
  = InstanceDecl spi li cx qcls insty <$> mapM (fixVarAnnotsDecl pls) ds
fixVarAnnotsDecl _ d = return d

fixVarAnnotsEquation :: [Pred] -> Equation PredType -> TCM (Equation PredType)
fixVarAnnotsEquation pls (Equation p mpty lhs rhs) = case mpty of
    Nothing                -> Equation p mpty lhs <$> fixVarAnnotsRhs pls rhs
    Just (PredType pls' _) -> Equation p mpty lhs
                              <$> fixVarAnnotsRhs (plUnion pls pls') rhs

fixVarAnnotsRhs :: [Pred] -> Rhs PredType -> TCM (Rhs PredType)
fixVarAnnotsRhs pls (SimpleRhs spi li e ds) =
  SimpleRhs spi li <$> fixVarAnnotsExpr pls e <*> mapM (fixVarAnnotsDecl pls) ds
fixVarAnnotsRhs pls (GuardedRhs spi li es ds) =
  GuardedRhs spi li <$> mapM (fixVarAnnotsCondExpr pls) es
                    <*> mapM (fixVarAnnotsDecl pls) ds

fixVarAnnotsCondExpr :: [Pred] -> CondExpr PredType -> TCM (CondExpr PredType)
fixVarAnnotsCondExpr pls (CondExpr spi g e)
  = CondExpr spi <$> fixVarAnnotsExpr pls g <*> fixVarAnnotsExpr pls e

fixVarAnnotsExpr :: [Pred] -> Expression PredType -> TCM (Expression PredType)
fixVarAnnotsExpr pls (Variable spi pty v) = do
  mid <- getModuleIdent
  vEnv <- getValueEnv
  thetaGlobal <- getTypeSubst
  let pty1@(PredType _ ty1) = subst thetaGlobal pty
  case funTypeSafe False mid v vEnv of
    Nothing -> return $ Variable spi pty v
    Just (ForAll _ pty2@(PredType pls2 ty2)) ->
        case matchPredTypeSafe pty2 pty1 idSubst of
          Just _  -> return $ Variable spi pty1 v
          Nothing -> let theta = fromJust $ matchTypeSafe ty2 ty1 idSubst
                         pls1' = filter (`plElem` pls) (subst theta pls2)
                     in return $ Variable spi (PredType pls1' ty1) v
fixVarAnnotsExpr pls (Paren spi e) = Paren spi <$> fixVarAnnotsExpr pls e
fixVarAnnotsExpr pls (Typed spi e qty)
  = Typed spi <$> fixVarAnnotsExpr pls e <*> return qty
fixVarAnnotsExpr pls (Record spi a c fs)
  = Record spi a c <$> mapM (fixVarAnnotsField pls) fs
fixVarAnnotsExpr pls (RecordUpdate spi e fs)
  = RecordUpdate spi <$> fixVarAnnotsExpr pls e
                     <*> mapM (fixVarAnnotsField pls) fs
fixVarAnnotsExpr pls (Tuple spi es)
  = Tuple spi <$> mapM (fixVarAnnotsExpr pls) es
fixVarAnnotsExpr pls (List spi a es)
  = List spi a <$> mapM (fixVarAnnotsExpr pls) es
fixVarAnnotsExpr pls (ListCompr spi e qs)
  = ListCompr spi <$> fixVarAnnotsExpr pls e <*> mapM (fixVarAnnotsStmt pls) qs
fixVarAnnotsExpr pls (EnumFrom spi e) = EnumFrom spi <$> fixVarAnnotsExpr pls e
fixVarAnnotsExpr pls (EnumFromThen spi e1 e2)
  = EnumFromThen spi <$> fixVarAnnotsExpr pls e1 <*> fixVarAnnotsExpr pls e2
fixVarAnnotsExpr pls (EnumFromTo spi e1 e2)
  = EnumFromTo spi <$> fixVarAnnotsExpr pls e1 <*> fixVarAnnotsExpr pls e2
fixVarAnnotsExpr pls (EnumFromThenTo spi e1 e2 e3) = EnumFromThenTo spi
                                                 <$> fixVarAnnotsExpr pls e1
                                                 <*> fixVarAnnotsExpr pls e2
                                                 <*> fixVarAnnotsExpr pls e3
fixVarAnnotsExpr pls (UnaryMinus spi e)
  = UnaryMinus spi <$> fixVarAnnotsExpr pls e
fixVarAnnotsExpr pls (Apply spi e1 e2)
  = Apply spi <$> fixVarAnnotsExpr pls e1 <*> fixVarAnnotsExpr pls e2
fixVarAnnotsExpr pls (InfixApply spi e1 op e2) =   InfixApply spi
                                              <$> fixVarAnnotsExpr pls e1
                                              <*> return op
                                              <*> fixVarAnnotsExpr pls e2
fixVarAnnotsExpr pls (LeftSection spi e op)
  = LeftSection spi <$> fixVarAnnotsExpr pls e <*> return op
fixVarAnnotsExpr pls (RightSection spi op e)
  = RightSection spi op <$> fixVarAnnotsExpr pls e
fixVarAnnotsExpr pls (Lambda spi ts e)
  = Lambda spi ts <$> fixVarAnnotsExpr pls e
fixVarAnnotsExpr pls (Let spi li ds e)
  = Let spi li <$> mapM (fixVarAnnotsDecl pls) ds <*> fixVarAnnotsExpr pls e
fixVarAnnotsExpr pls (Do spi li sts e)
  = Do spi li <$> mapM (fixVarAnnotsStmt pls) sts <*> fixVarAnnotsExpr pls e
fixVarAnnotsExpr pls (IfThenElse spi e1 e2 e3) = IfThenElse spi
                                              <$> fixVarAnnotsExpr pls e1
                                              <*> fixVarAnnotsExpr pls e2
                                              <*> fixVarAnnotsExpr pls e3
fixVarAnnotsExpr pls (Case spi li ct e as)
  = Case spi li ct <$> fixVarAnnotsExpr pls e <*> mapM (fixVarAnnotsAlt pls) as
fixVarAnnotsExpr _ e = return e

fixVarAnnotsField :: [Pred] -> Field (Expression PredType)
                -> TCM (Field (Expression PredType))
fixVarAnnotsField pls (Field spi qid e)
  = Field spi qid <$> fixVarAnnotsExpr pls e

fixVarAnnotsAlt :: [Pred] -> Alt PredType -> TCM (Alt PredType)
fixVarAnnotsAlt pls (Alt spi t rhs) = Alt spi t <$> fixVarAnnotsRhs pls rhs

fixVarAnnotsStmt :: [Pred] -> Statement PredType -> TCM (Statement PredType)
fixVarAnnotsStmt pls (StmtExpr spi e) = StmtExpr spi <$> fixVarAnnotsExpr pls e
fixVarAnnotsStmt pls (StmtDecl spi li ds)
  = StmtDecl spi li <$> mapM (fixVarAnnotsDecl pls) ds
fixVarAnnotsStmt pls (StmtBind spi t e)
  = StmtBind spi t <$> fixVarAnnotsExpr pls e

-- Instantiation and Generalization:
-- We use negative offsets for fresh type variables.

fresh :: (Int -> a) -> TCM a
fresh f = f <$> getNextId

freshVar :: (Int -> a) -> TCM a
freshVar f = fresh $ \n -> f (- n)

freshTypeVar :: TCM Type
freshTypeVar = freshVar TypeVariable

-- Returns a fresh type predicated by each type class in the given list.
-- Note that this method only works with unary type classes.
freshPredType :: [QualIdent] -> TCM (PredList, Type)
freshPredType qclss = do
  ty <- freshTypeVar
  return
    (foldr (\qcls -> plInsert (Pred OPred qcls [ty])) [] qclss, ty)

freshEnumType :: TCM (PredList, Type)
freshEnumType = freshPredType [qEnumId]

freshNumType :: TCM (PredList, Type)
freshNumType = freshPredType [qNumId]

freshFractionalType :: TCM (PredList, Type)
freshFractionalType = freshPredType [qFractionalId]

freshMonadType :: TCM (PredList, Type)
freshMonadType = freshPredType [qMonadId]

freshMonadFailType :: TCM (PredList, Type)
freshMonadFailType = freshPredType [qMonadFailId]

freshDataType :: TCM (PredList, Type)
freshDataType = freshPredType [qDataId]

freshConstrained :: [Type] -> TCM Type
freshConstrained = freshVar . TypeConstrained

dataPred :: Type -> Pred
dataPred ty = Pred OPred qDataId [ty]

-- TODO: Are there any changes necessary for this function to work with multi-
--         parameter type classes?
inst :: TypeScheme -> TCM (PredList, Type)
inst (ForAll n (PredType pls ty)) = do
  tys <- replicateM n freshTypeVar
  return (expandAliasType tys pls, expandAliasType tys ty)

-- The function 'skol' instantiates the type of data and newtype
-- constructors in patterns. All universally quantified type variables
-- are instantiated with fresh type variables and all existentially
-- quantified type variables are instantiated with fresh skolem types.
-- All constraints that appear on the right hand side of the
-- constructor's declaration are added to the dynamic instance
-- environment.

skol :: TypeScheme -> TCM (PredList, Type)
skol (ForAll n (PredType pls ty)) = do
  tys <- replicateM n freshTypeVar
  clsEnv <- getClassEnv
  modifyInstEnv $
    fmap $ bindSkolemInsts $ expandAliasType tys $ maxPredList clsEnv pls
  return ([], expandAliasType tys ty)
  where bindSkolemInsts = flip (foldr bindSkolemInst)
        bindSkolemInst (Pred _ qcls tys) dInEnv =
          Map.insert qcls ((tys,True) : fromMaybe [] (Map.lookup qcls dInEnv)) dInEnv

-- The function 'gen' generalizes a predicate set ps and a type tau into
-- a type scheme forall alpha . ps -> tau by universally quantifying all
-- type variables that are free in tau and not fixed by the environment.
-- The set of the latter is given by gvs.

gen :: Set.Set Int -> LPredList -> Type -> TypeScheme
gen gvs pls ty = ForAll (length tvs) (subst theta pty)
  where pty = PredType (map getPred pls) ty
        tvs = [tv | tv <- nub (typeVars pty), tv `Set.notMember` gvs]
        tvs' = map TypeVariable [0 ..]
        theta = foldr2 bindSubst idSubst tvs tvs'

-- Auxiliary Functions:
-- The functions 'constrType', 'varType', 'funType' and 'labelType' are used
-- to retrieve the type of constructors, pattern variables, variables and
-- labels in expressions, respectively, from the value environment. Because
-- the syntactical correctness has already been verified by the syntax checker,
-- none of these functions should fail.

-- Note that 'varType' can handle ambiguous identifiers and returns the first
-- available type. This function is used for looking up the type of an
-- identifier on the left hand side of a rule where it unambiguously refers
-- to the local definition.

-- The function 'constrLabels' returns a list of all labels belonging to a
-- data constructor. The function 'varArity' works like 'varType' but returns
-- a variable's arity instead of its type.

-- The function 'funType' has an additional boolean parameter which marks
-- whether the implicit class constraint of the requested function, if it has
-- any, should be transformed into a regular predicate. This functionality
-- should be used when using this type information to infer and check the types
-- of expressions and patterns that could contain class methods. It should only
-- be disabled if the implicit class constraint of a requested class method has
-- to be treated differently than other predicates.

constrType :: ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
constrType m c vEnv = case qualLookupValue c vEnv of
  [DataConstructor  _ _ _ tySc] -> tySc
  [NewtypeConstructor _ _ tySc] -> tySc
  _ -> case qualLookupValue (qualQualify m c) vEnv of
    [DataConstructor  _ _ _ tySc] -> tySc
    [NewtypeConstructor _ _ tySc] -> tySc
    _ -> internalError $ "TypeCheck.constrType: " ++ show c

constrLabels :: ModuleIdent -> QualIdent -> ValueEnv -> [Ident]
constrLabels m c vEnv = case qualLookupValue c vEnv of
  [DataConstructor _ _ ls _] -> ls
  [NewtypeConstructor _ l _] -> [l]
  _ -> case qualLookupValue (qualQualify m c) vEnv of
    [DataConstructor _ _ ls _] -> ls
    [NewtypeConstructor _ l _] -> [l]
    _ -> internalError $ "TypeCheck.constrLabels: " ++ show c

varType :: Ident -> ValueEnv -> TypeScheme
varType v vEnv = case lookupValue v vEnv of
  Value _ _ _ tySc : _ -> tySc
  _ -> internalError $ "TypeCheck.varType: " ++ show v

varArity :: QualIdent -> ValueEnv -> Int
varArity v vEnv = case qualLookupValue v vEnv of
  Value _ _ n _ : _ -> n
  Label {}      : _ -> 1
  _ -> internalError $ "TypeCheck.varArity: " ++ show v

funType :: Bool -> ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
funType False m f vEnv = case qualLookupValue f vEnv of
  [Value _ _ _ tySc] -> tySc
  [Label _ _ tySc] -> tySc
  _ -> case qualLookupValue (qualQualify m f) vEnv of
    [Value _ _ _ tySc] -> tySc
    [Label _ _ tySc] -> tySc
    _ -> internalError $ "TypeCheck.funType: " ++ show f
funType True  m f vEnv = let ForAll n (PredType pls ty) = funType False m f vEnv
                         in  ForAll n (PredType (removeICCFlagList pls) ty)

funTypeSafe :: Bool -> ModuleIdent -> QualIdent -> ValueEnv -> Maybe TypeScheme
funTypeSafe False m f vEnv = case qualLookupValue f vEnv of
  [Value _ _ _ tySc] -> Just tySc
  [Label _ _ tySc] -> Just tySc
  _ -> case qualLookupValue (qualQualify m f) vEnv of
    [Value _ _ _ tySc] -> Just tySc
    [Label _ _ tySc] -> Just tySc
    _ -> Nothing
funTypeSafe True  m f vEnv = remICC <$> funTypeSafe False m f vEnv
  where remICC (ForAll n (PredType pls ty)) =
          ForAll n (PredType (removeICCFlagList pls) ty)

labelType :: ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
labelType m l vEnv = case qualLookupValue l vEnv of
  [Label _ _ tySc] -> tySc
  _ -> case qualLookupValue (qualQualify m l) vEnv of
    [Label _ _ tySc] -> tySc
    _ -> internalError $ "TypeCheck.labelType: " ++ show l

-- The function 'expandPoly' handles the expansion of type aliases. It expects
-- none of the type constraints in its argument to be an implicit class
-- constraint.

expandPoly :: QualTypeExpr -> TCM PredType
expandPoly = expandPolyICC OPred

-- Like 'expandPoly' but with an additional parameter marking whether the first
-- type constraint in the qualified type expression given is an implicit class
-- constraint.
expandPolyICC :: PredIsICC -> QualTypeExpr -> TCM PredType
expandPolyICC fstIcc qty = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  clsEnv <- getClassEnv
  return $ expandPolyType fstIcc m tcEnv clsEnv qty

-- The function 'splitPredSetAny' splits a predicate set into a pair of
-- predicate sets such that every predicate containing at least one of the given
-- set of type variables is in the first returned predicate set.

-- 'splitPredSetAll' is similar, but the predicates in the first predicate set
-- contain only type variables that are in the given set of type variables, but
-- at least one of them.

splitPredListAny :: IsPred a => Set.Set Int -> [a] -> ([a], [a])
splitPredListAny fvs = partition $ any (`Set.member` fvs) . typeVars

splitPredListAll :: IsPred a => Set.Set Int -> [a] -> ([a], [a])
splitPredListAll fvs = partition $
  (\vs -> not (null vs) && all (`Set.member` fvs) vs) . typeVars

-- The functions 'fvEnv' and 'fsEnv' compute the set of free type variables
-- and free skolems of a type environment, respectively. We ignore the types
-- of data constructors here because we know that they are closed.

fvEnv :: ValueEnv -> Set.Set Int
fvEnv vEnv =
  Set.fromList [tv | tySc <- localTypes vEnv, tv <- typeVars tySc, tv < 0]

computeFvEnv :: TCM (Set.Set Int)
computeFvEnv = do
  theta <- getTypeSubst
  fvEnv . subst theta <$> getValueEnv

localTypes :: ValueEnv -> [TypeScheme]
localTypes vEnv = [tySc | (_, Value _ _ _ tySc) <- localBindings vEnv]

-- ---------------------------------------------------------------------------
-- Error functions
-- ---------------------------------------------------------------------------

errPolymorphicVar :: Ident -> Message
errPolymorphicVar v = spanInfoMessage v $ hsep $ map text
  ["Variable", idName v, "has a polymorphic type"]

errTypeSigTooGeneral :: ModuleIdent -> Doc -> QualTypeExpr
                     -> TypeScheme -> Message
errTypeSigTooGeneral m what qty tySc = spanInfoMessage qty $ vcat
  [ text "Type signature too general", what
  , text "Inferred type:"  <+> ppTypeScheme m tySc
  , text "Type signature:" <+> pPrint qty
  ]

errMethodTypeTooSpecific :: HasSpanInfo a => a -> ModuleIdent -> Doc -> PredType
                         -> TypeScheme -> Message
errMethodTypeTooSpecific p m what pty tySc = spanInfoMessage p $ vcat
  [ text "Method type too specific", what
  , text "Inferred type:" <+> ppTypeScheme m tySc
  , text "Expected type:" <+> ppPredType m pty
  ]

errNonFunctionType :: HasSpanInfo a => a -> String -> Doc -> ModuleIdent -> Type
                   -> Message
errNonFunctionType p what doc m ty = spanInfoMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be applied"
  ]

errNonBinaryOp :: HasSpanInfo a => a -> String -> Doc -> ModuleIdent -> Type
               -> Message
errNonBinaryOp p what doc m ty = spanInfoMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be used as binary operator"
  ]

errTypeMismatch :: HasSpanInfo a => a -> String -> Doc -> ModuleIdent -> Type
                -> Type -> Doc -> Message
errTypeMismatch p what doc m ty1 ty2 reason = spanInfoMessage p $ vcat
  [ text "Type error in"  <+> text what, doc
  , text "Inferred type:" <+> ppType m ty2
  , text "Expected type:" <+> ppType m ty1
  , reason
  ]

errSkolemFieldLabel :: HasSpanInfo a => a -> Ident -> Message
errSkolemFieldLabel p l = spanInfoMessage p $ hsep $ map text
  ["Existential type escapes with type of record selector", escName l]

errRecursiveType :: ModuleIdent -> Int -> Type -> Doc
errRecursiveType m tv = errIncompatibleTypes m (TypeVariable tv)

errIncompatibleTypes :: ModuleIdent -> Type -> Type -> Doc
errIncompatibleTypes m ty1 ty2 = sep
  [ text "Types" <+> ppType m ty1
  , nest 2 $ text "and" <+> ppType m ty2
  , text "are incompatible"
  ]

errIncompatibleLabelTypes :: HasSpanInfo a => a -> ModuleIdent -> Ident -> Type
                          -> Type -> Message
errIncompatibleLabelTypes p m l ty1 ty2 = spanInfoMessage p $ sep
  [ text "Labeled types" <+> ppIdent l <+> text "::" <+> ppType m ty1
  , nest 10 $ text "and" <+> ppIdent l <+> text "::" <+> ppType m ty2
  , text "are incompatible"
  ]

-- taken from Leif-Erik Krueger
errMissingInstance :: ModuleIdent -> LPred -> Message
errMissingInstance m (LPred pr p what doc) = spanInfoMessage p $ vcat
  [ text "Missing instance for" <+> ppPred m pr
  , text "arising from" <+> text what
  , doc
  ]

-- taken from Leif-Erik Krueger
errInstanceOverlap :: ModuleIdent -> LPred -> [InstMatchInfo] -> Bool -> Message
errInstanceOverlap m (LPred pr@(Pred _ qcls _) p what doc) insts tvChoice =
  spanInfoMessage p $ vcat $
    [ text "Instance overlap for" <+> ppPred m pr
    , text "arising from" <+> text what
    , doc
    , text "Matching instances:"
    , nest 2 $ vcat $ map displayMatchingInst insts
    ] ++ if tvChoice then [ text "(The choice depends on the"
                          , text "instantiation of type variables.)" ]
                     else []
 where
  displayMatchingInst :: InstMatchInfo -> Doc
  displayMatchingInst (m', _, itys, _, _) =
    ppPred m (Pred OPred qcls itys) <+> text "from" <+> pPrint m'

errFlexibleContext :: HasSpanInfo a => ModuleIdent -> a -> String -> Ident
                   -> Pred -> Message
errFlexibleContext m p what v pr = spanInfoMessage p $ vcat
  [ text "Constraint with non-variable argument" <+> ppPred m pr
  , text "occurring in the context of the inferred type for" <+> text what <+>
      text (escName v)
  , text "Use FlexibleContexts if you want do disable this."
  ]

errAmbiguousTypeVariable :: HasSpanInfo a => ModuleIdent -> a -> String -> Doc
                         -> LPredList -> Type -> Int -> Message
errAmbiguousTypeVariable m p what doc pls ty tv = spanInfoMessage p $ vcat
  [ text "Ambiguous type variable" <+> ppType m (TypeVariable tv)
  , text "in type" <+> ppPredType m (PredType (map getPred pls) ty)
  , text "inferred for" <+> text what
  , doc
  ]

{- HLINT ignore "Reduce duplication" -}
