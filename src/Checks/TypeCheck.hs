{-|
Module      : Checks.TypeCheck
Description : Type checking of Curry programs
Copyright   : (c) 1999–2004 Wolfgang Lux, Martin Engelke
                  2011–2015 Björn Peemöller
                  2014–2015 Jan Tikovsky
                  2016–2017 Finn Teegen
                  2019 Jan-Hendrik Matthes
License     : BSD-3-Clause

Maintainer  : fte@informatik.uni-kiel.de
Stability   : experimental
Portability : portable

This module implements the type checker of the Curry compiler. The type checker
is invoked after the syntactic correctness of the program has been verified and
kind checking has been applied to all type expressions. Local variables have
been renamed already. Thus, the compiler can maintain a flat type environment.
The type checker now checks the correct typing of all expressions and also
verifies that the type signatures given by the user match the inferred types.
The type checker uses the algorithm by Damas and Milner (1982) for inferring
the types of unannotated declarations, but allows for polymorphic recursion
when a type annotation is present.

The result of type checking is a (flat) top-level environment containing the
types of all constructors, variables, and functions defined at the top level of
a module. In addition, a type annotated source module is returned. Note that
type annotations on the left hand side of a declaration hold the function or
variable's generalized type with the type scheme's universal quantifier left
implicit. Type annotations on the right hand side of a declaration hold the
particular instance at which a polymorphic function or variable is used.
-}

{-# LANGUAGE CPP #-}

module Checks.TypeCheck (typeCheck) where

#if __GLASGOW_HASKELL__ >= 804
import           Prelude             hiding ((<>))
#endif

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative ((<$>), (<*>))
#endif
import           Control.Monad.Extra (allM, filterM, foldM, liftM, notM,
                                      replicateM, unless, unlessM, (&&^))
import qualified Control.Monad.State as S (State, gets, modify, runState)
import           Data.Foldable       (foldrM)
import           Data.Function       (on)
import           Data.List           (nub, nubBy, partition, sortBy)
import qualified Data.Map            as Map (Map, empty, insert, lookup)
import           Data.Maybe          (fromJust, isJust)
import qualified Data.Set.Extra      as Set (Set, concatMap, deleteMin, empty,
                                             fromList, insert, member,
                                             notMember, partition, singleton,
                                             toAscList, toList, union, unions)

import           Curry.Base.Ident
import           Curry.Base.Position
import           Curry.Base.Pretty
import           Curry.Base.SpanInfo
import           Curry.Syntax
import           Curry.Syntax.Pretty

import           Base.CurryTypes
import           Base.Expr
import           Base.Kinds
import           Base.Messages       (Message, internalError, posMessage)
import           Base.SCC
import           Base.TopEnv
import           Base.TypeExpansion
import           Base.Types
import           Base.TypeSubst
import           Base.Utils          (foldr2, fst3, mapAccumM, snd3, thd3,
                                      uncurry3)

import           Env.Class
import           Env.Instance
import           Env.TypeConstructor
import           Env.Value

-- | Type checking proceeds as follows. First, the types of all data
-- constructors, field labels and class methods are entered into the value
-- environment and then a type inference for all function and value definitions
-- is performed.
typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> InstEnv -> [Decl a]
          -> ([Decl Type], ValueEnv, [Message])
typeCheck m tcEnv vEnv clsEnv inEnv ds = runTCM (checkDecls ds) initState
  where
    initState = TcState m tcEnv vEnv clsEnv (inEnv, Map.empty)
                        [intType, floatType] idSubst emptySigEnv 1 []

checkDecls :: [Decl a] -> TCM [Decl Type]
checkDecls ds = do
  bindConstrs
  mapM_ checkFieldLabel (filter isTypeDecl ds) &&> bindLabels
  bindClassMethods
  mapM_ setDefaults $ filter isDefaultDecl ds
  bpds' <- snd <$> tcPDecls bpds
  tpds' <- mapM tcTopPDecl tpds
  theta <- getTypeSubst
  return $ map (fmap $ subst theta) $ fromPDecls $ tpds' ++ bpds'
  where
    (bpds, tpds) = partition (isBlockDecl . snd) $ toPDecls ds

-- -----------------------------------------------------------------------------
-- Type Check Monad
-- -----------------------------------------------------------------------------

-- The type checker makes use of a state monad in order to maintain the value
-- environment, the current substitution, and a counter which is used for
-- generating fresh type variables.

-- Additionally, an extended instance environment is used in order to handle the
-- introduction of local instances when matching a data constructor with a
-- non-empty context. This extended instance environment is composed of the
-- static top-level environment and a dynamic environment that maps each class
-- on the instances which are in scope for it. The rationale behind using this
-- representation is that it makes it easy to apply the current substitution to
-- the dynamic part of the environment.

type TCM = S.State TcState

type InstEnv' = (InstEnv, Map.Map QualIdent [Type])

data TcState = TcState
  { moduleIdent  :: ModuleIdent -- read-only
  , tyConsEnv    :: TCEnv
  , valueEnv     :: ValueEnv
  , classEnv     :: ClassEnv
  , instEnv      :: InstEnv'    -- instances (static and dynamic)
  , defaultTypes :: [Type]
  , typeSubst    :: TypeSubst
  , sigEnv       :: SigEnv
  , nextId       :: Int         -- automatic counter
  , errors       :: [Message]
  }

(&&>) :: TCM () -> TCM () -> TCM ()
pre &&> suf = do
  errs <- pre >> S.gets errors
  if null errs then suf else return ()

(>>-) :: TCM (a, b, c) -> (a -> b -> TCM a) -> TCM (a, c)
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
runTCM tcm s = let (a, s') = S.runState tcm s
                in (a, typeSubst s' `subst` valueEnv s', reverse $ errors s')

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
  n <- S.gets nextId
  S.modify $ \s -> s { nextId = succ n }
  return n

report :: Message -> TCM ()
report err = S.modify $ \s -> s { errors = err : errors s }

ok :: TCM ()
ok = return ()

-- -----------------------------------------------------------------------------
-- Numbered declarations
-- -----------------------------------------------------------------------------

-- Because the type check may mess up the order of the declarations, we
-- associate each declaration with a number. At the end of the type check, we
-- can use these numbers to restore the original declaration order.

type PDecl a = (Int, Decl a)

toPDecls :: [Decl a] -> [PDecl a]
toPDecls = zip [0..]

fromPDecls :: [PDecl a] -> [Decl a]
fromPDecls = map snd . sortBy (compare `on` fst)

-- During the type check we also have to convert the type of declarations
-- without annotations, which is done by the function 'untyped' below.

untyped :: PDecl a -> PDecl b
untyped = fmap $ fmap $ internalError "TypeCheck.untyped"

-- In the next step, the types of all data constructors are entered into
-- the value environment using the information entered into the type constructor
-- environment before.

-- -----------------------------------------------------------------------------
-- Binding data constructors
-- -----------------------------------------------------------------------------

bindConstrs :: TCM ()
bindConstrs = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindConstrs' m tcEnv

-- | Returns the type for the given type constructor with the given arity.
constrType' :: QualIdent -> Int -> Type
constrType' tc n
  = applyType (TypeConstructor tc) $ map TypeVariable [0 .. n - 1]

-- | Returns the type of the data constructor with the given result type and
-- the given argument types.
dataConstrType :: Int -> Type -> [Type] -> Type
dataConstrType n ty tys = TypeForall [0 .. n - 1] $ foldr TypeArrow ty tys

-- | Returns the type of the newtype data constructor with the given result
-- type and the given argument type.
newConstrType :: Int -> Type -> Type -> Type
newConstrType n lty cty = TypeForall [0 .. n - 1] $ TypeArrow lty cty

bindConstrs' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindConstrs' m tcEnv vEnv = foldr (bindData . snd) vEnv $ localBindings tcEnv
  where
    bindData (DataType tc k cs)    vEnv' = let n = kindArity k in
      foldr (bindConstr m n (constrType' tc n)) vEnv' cs
    bindData (RenamingType tc k c) vEnv' = let n = kindArity k in
      bindNewConstr m n (constrType' tc n) c vEnv'
    bindData _                     vEnv' = vEnv'

bindConstr :: ModuleIdent -> Int -> Type -> DataConstr -> ValueEnv -> ValueEnv
bindConstr m n ty (DataConstr c tys)
  = bindGlobalInfo (\qc tySc -> DataConstructor qc arity ls tySc) m c
                   (dataConstrType n ty tys)
  where
    arity = length tys
    ls = replicate arity anonId
bindConstr m n ty (RecordConstr c ls tys)
  = bindGlobalInfo (\qc tySc -> DataConstructor qc (length tys) ls tySc) m c
                   (dataConstrType n ty tys)

bindNewConstr :: ModuleIdent -> Int -> Type -> DataConstr -> ValueEnv
              -> ValueEnv
bindNewConstr m n cty (DataConstr c [lty])
  = bindGlobalInfo (\qc tySc -> NewtypeConstructor qc anonId tySc) m c
                   (newConstrType n lty cty)
bindNewConstr m n cty (RecordConstr c [l] [lty])
  = bindGlobalInfo (\qc tySc -> NewtypeConstructor qc l tySc) m c
                   (newConstrType n lty cty)
bindNewConstr _ _ _   _
  = internalError "TypeCheck.bindNewConstr: newtype with illegal constructors"

-- -----------------------------------------------------------------------------
-- Binding labels
-- -----------------------------------------------------------------------------

-- When a field label occurs in more than one constructor declaration of a data
-- type, the compiler ensures that the label is defined consistently, i.e. both
-- occurrences have the same type.

checkFieldLabel :: Decl a -> TCM ()
checkFieldLabel (DataDecl _ _ tvs cs _) = do
  ls <- mapM (tcFieldLabel tvs) labels
  mapM_ tcFieldLabels (groupLabels ls)
  where
    labels = [(l, p, ty) | RecordDecl _ _ fs <- cs,
                           FieldDecl p ls' ty <- fs, l <- ls']
checkFieldLabel (NewtypeDecl _ _ tvs (NewRecordDecl p _ (l, ty)) _)
  = tcFieldLabel tvs (l, p, ty) >> ok
checkFieldLabel _ = ok

tcFieldLabel :: HasPosition p => [Ident] -> (Ident, p, TypeExpr)
             -> TCM (Ident, p, Type)
tcFieldLabel tvs (l, p, ty) = (,,) l p <$> expandMono tvs ty

groupLabels :: Eq a => [(a, b, c)] -> [(a, b, [c])]
groupLabels []               = []
groupLabels ((x, y, z):xyzs) = (x, y, z : map thd3 xyzs') : groupLabels xyzs''
  where
    (xyzs', xyzs'') = partition ((x ==) . fst3) xyzs

tcFieldLabels :: HasPosition p => (Ident, p, [Type]) -> TCM ()
tcFieldLabels (_, _, [])     = ok
tcFieldLabels (l, p, ty:tys) = unless (not (any (ty /=) tys)) $ do
  m <- getModuleIdent
  report $ errIncompatibleLabelTypes p m l ty (head tys)

-- Next, the types of all field labels are added to the value environment.

bindLabels :: TCM ()
bindLabels = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindLabels' m tcEnv

bindLabels' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindLabels' m tcEnv vEnv = foldr (bindData . snd) vEnv $ localBindings tcEnv
  where
    bindData (DataType tc k cs)                             vEnv'
      = foldr (bindLabel m n (constrType' tc n)) vEnv' $ nubBy sameLabel clabels
      where
        n = kindArity k
        labels = zip (concatMap recLabels cs) (concatMap recLabelTypes cs)
        clabels = [(l, constr l, ty) | (l, ty) <- labels]
        constr l = map (qualifyLike tc)
                       [constrIdent c | c <- cs, l `elem` recLabels c]
        sameLabel (l1, _, _) (l2, _, _) = l1 == l2
    bindData (RenamingType tc k (RecordConstr c [l] [lty])) vEnv'
      = bindLabel m n (constrType' tc n) (l, [qc], lty) vEnv'
      where
        n = kindArity k
        qc = qualifyLike tc c
    bindData (RenamingType _ _ (RecordConstr _ _ _))        _
      = internalError $ "TypeCheck.bindLabels'.bindData: " ++
          "RenamingType with more than one record label"
    bindData _                                              vEnv' = vEnv'

bindLabel :: ModuleIdent -> Int -> Type -> (Ident, [QualIdent], Type)
          -> ValueEnv -> ValueEnv
bindLabel m n ty (l, lcs, lty)
  = bindGlobalInfo (\qc tySc -> Label qc lcs tySc) m l
                   (TypeForall [0 .. n - 1] (TypeArrow ty lty))

-- -----------------------------------------------------------------------------
-- Binding class methods
-- -----------------------------------------------------------------------------

-- Last, the types of all class methods are added to the value environment.

bindClassMethods :: TCM ()
bindClassMethods = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindClassMethods' m tcEnv

bindClassMethods' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindClassMethods' m tcEnv vEnv
  = foldr (bindMethods . snd) vEnv $ localBindings tcEnv
  where
    bindMethods (TypeClass _ _ ms) vEnv' = foldr (bindClassMethod m) vEnv' ms
    bindMethods _                  vEnv' = vEnv'

-- Since the implementations of class methods can differ in their arity, we
-- assume an arity of 0 when we enter one into the value environment.

bindClassMethod :: ModuleIdent -> ClassMethod -> ValueEnv -> ValueEnv
bindClassMethod m (ClassMethod f _ ty) =
  bindGlobalInfo (\qc tySc -> Value qc True 0 tySc) m f (typeScheme ty)

-- -----------------------------------------------------------------------------
-- Default Types
-- -----------------------------------------------------------------------------

-- The list of default types is given either by a default declaration in the
-- source code or defaults to the predefined list of numeric data types.

setDefaults :: Decl a -> TCM ()
setDefaults (DefaultDecl _ tys) = mapM toDefaultType tys >>= setDefaultTypes
  where
    toDefaultType = liftM snd . (inst =<<) . liftM typeScheme . expandMono []
setDefaults _                   = ok

-- -----------------------------------------------------------------------------
-- Type Signatures
-- -----------------------------------------------------------------------------

-- The type checker collects type signatures in a flat environment. The types
-- are not expanded so that the signature is available for use in the error
-- message that is printed when the inferred type is less general than the
-- signature.

type SigEnv = Map.Map Ident TypeExpr

emptySigEnv :: SigEnv
emptySigEnv = Map.empty

bindTypeSig :: Ident -> TypeExpr -> SigEnv -> SigEnv
bindTypeSig = Map.insert

bindTypeSigs :: Decl a -> SigEnv -> SigEnv
bindTypeSigs (TypeSig _ vs ty) env = foldr (flip bindTypeSig ty) env vs
bindTypeSigs _                 env = env

lookupTypeSig :: Ident -> SigEnv -> Maybe TypeExpr
lookupTypeSig = Map.lookup

-- -----------------------------------------------------------------------------
-- Type Check Mode
-- -----------------------------------------------------------------------------

-- | Either infer the type of an expression or check that an expression has a
-- specific type.
data CheckMode = Infer | Check Type

-- -----------------------------------------------------------------------------
-- Declaration groups
-- -----------------------------------------------------------------------------

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

tcDecls :: [Decl a] -> TCM (PredSet, [Decl Type])
tcDecls = liftM (fmap fromPDecls) . tcPDecls . toPDecls

tcPDecls :: [PDecl a] -> TCM (PredSet, [PDecl Type])
tcPDecls pds = withLocalSigEnv $ do
  let (vpds, opds) = partition (isValueDecl . snd) pds
  setSigEnv $ foldr (bindTypeSigs . snd) emptySigEnv $ opds
  m <- getModuleIdent
  (ps, vpdss') <- mapAccumM tcPDeclGroup emptyPredSet
                            (scc (bv . snd) (qfv m . snd) vpds)
  return (ps, map untyped opds ++ concat (vpdss' :: [[PDecl Type]]))

tcPDeclGroup :: PredSet -> [PDecl a] -> TCM (PredSet, [PDecl Type])
tcPDeclGroup ps [(i, ExternalDecl p fs)] = do
  tys <- mapM (tcExternal . varIdent) fs
  return (ps, [(i, ExternalDecl p (zipWith (fmap . const) tys fs))])
tcPDeclGroup ps [(i, FreeDecl p fvs)]    = do
  vs <- mapM (tcDeclVar False) (bv fvs)
  m <- getModuleIdent
  modifyValueEnv $ flip (bindVars m) vs
  return (ps, [(i, FreeDecl p (map (\(v, _, tySc) -> Var (rawPredType tySc) v)
                                   vs))])
tcPDeclGroup ps pds                      = do
  vEnv <- getValueEnv
  vss <- mapM (tcDeclVars . snd) pds
  m <- getModuleIdent
  modifyValueEnv $ flip (bindVars m) $ concat vss
  sigs <- getSigEnv
  let (impPds, expPds) = partitionPDecls sigs pds
  (ps', impPds') <- mapAccumM tcPDecl ps impPds
  theta <- getTypeSubst
  tvs <- liftM (concatMap $ typeVars . subst theta . fst) $
           filterM (notM . isNonExpansive . snd . snd) impPds'
  let fvs = foldr Set.insert (fvEnv (subst theta vEnv)) tvs
      (gps, lps) = splitPredSet fvs ps'
  lps' <- foldM (uncurry . defaultPDecl fvs) lps impPds'
  theta' <- getTypeSubst
  let impPds'' = map (uncurry (fixType . gen fvs lps' . subst theta')) impPds'
  modifyValueEnv $ flip (rebindVars m) (concatMap (declVars . snd) impPds'')
  (ps'', expPds') <- mapAccumM (uncurry . tcCheckPDecl) gps expPds
  return (ps'', impPds'' ++ expPds')

partitionPDecls :: SigEnv -> [PDecl a] -> ([PDecl a], [(TypeExpr, PDecl a)])
partitionPDecls sigs =
  foldr (\pd -> maybe (implicit pd) (explicit pd) (typeSig $ snd pd)) ([], [])
  where implicit pd ~(impPds, expPds) = (pd : impPds, expPds)
        explicit pd qty ~(impPds, expPds) = (impPds, (qty, pd) : expPds)
        typeSig (FunctionDecl _ _ f _) = lookupTypeSig f sigs
        typeSig (PatternDecl _ (VariablePattern _ _ v) _) = lookupTypeSig v sigs
        typeSig _ = Nothing

bindVars :: ModuleIdent -> ValueEnv -> [(Ident, Int, Type)] -> ValueEnv
bindVars m = foldr $ uncurry3 $ flip (bindFun m) False

rebindVars :: ModuleIdent -> ValueEnv -> [(Ident, Int, Type)] -> ValueEnv
rebindVars m = foldr $ uncurry3 $ flip (rebindFun m) False

tcDeclVars :: Decl a -> TCM [(Ident, Int, Type)]
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
  _                     -> mapM (tcDeclVar False) (bv t)
tcDeclVars _ = internalError "TypeCheck.tcDeclVars"

tcDeclVar :: Bool -> Ident -> TCM (Ident, Int, Type)
tcDeclVar poly v = do
  sigs <- getSigEnv
  case lookupTypeSig v sigs of
    Just qty
      | poly || null (fv qty) -> do
        pty <- expandPoly qty
        return (v, 0, typeScheme pty)
      | otherwise -> do
        report $ errPolymorphicVar v
        lambdaVar v
    Nothing -> lambdaVar v

tcPDecl :: PredSet -> PDecl a -> TCM (PredSet, (Type, PDecl Type))
tcPDecl ps (i, FunctionDecl p _ f eqs) = do
  vEnv <- getValueEnv
  tcFunctionPDecl i ps (varType f vEnv) p f eqs
tcPDecl ps (i, d@(PatternDecl p t rhs)) = do
  (ps', ty', t') <- tcPattern p t
  (ps'', rhs') <- tcRhs Infer rhs >>-
    unifyDecl p "pattern declaration" (ppDecl d) (ps `Set.union` ps') ty'
  return (ps'', (ty', (i, PatternDecl p t' rhs')))
tcPDecl _ _ = internalError "TypeCheck.tcPDecl"

-- The function 'tcFunctionPDecl' ignores the context of a function's type
-- signature. This prevents missing instance errors when the inferred type
-- of a function is less general than the declared type.

tcFunctionPDecl :: Int -> PredSet -> Type -> SpanInfo -> Ident
                -> [Equation a] -> TCM (PredSet, (Type, PDecl Type))
tcFunctionPDecl i ps tySc p f eqs = do
  (_, ty) <- inst tySc
  (ps', eqs') <- mapAccumM (tcEquation ty) ps eqs
  return (ps', (ty, (i, FunctionDecl p (rawPredType tySc) f eqs')))

tcEquation :: Type -> PredSet -> Equation a
           -> TCM (PredSet, Equation Type)
tcEquation ty ps eqn@(Equation p lhs rhs) =
  tcEqn ty p lhs rhs >>- unifyDecl p "equation" (ppEquation eqn) ps ty

tcEqn :: Type -> SpanInfo -> Lhs a -> Rhs a
      -> TCM (PredSet, Type, Equation Type)
tcEqn tySig p lhs rhs = do
  (ps, tys, lhs', ps', ty, rhs') <- withLocalValueEnv $ do
    let (argTys, _) = arrowUnapply tySig
    bindLhsVars argTys lhs
    (ps, tys, lhs') <- tcLhs p lhs
    (ps', ty, rhs') <- tcRhs Infer rhs
    return (ps, tys, lhs', ps', ty, rhs')
  ps'' <- reducePredSet p "equation" (ppEquation (Equation p lhs' rhs'))
                        (ps `Set.union` ps')
  return (ps'', foldr TypeArrow ty tys, Equation p lhs' rhs')

bindLhsVars :: [Type] -> Lhs a -> TCM ()
bindLhsVars tys (FunLhs _ _ ts) = do
  mapM_ (uncurry bindPatternVars) $ zip (map Check tys ++ repeat Infer) ts
bindLhsVars tys (OpLhs _ t1 op t2)
  = bindLhsVars tys (FunLhs NoSpanInfo op [t1, t2])
bindLhsVars tys (ApLhs _ lhs ps)
  = do let (tys1, tys2) = splitAt (length ps) tys
       mapM_ (uncurry bindPatternVars) $ zip (map Check tys2) ps
       bindLhsVars tys1 lhs

bindPatternVars :: CheckMode -> Pattern a -> TCM ()
bindPatternVars Infer      (VariablePattern _ _ v)       = do
  m <- getModuleIdent
  ty <- lambdaVar v
  modifyValueEnv $ flip (bindVars m) [ty]
bindPatternVars (Check ty) (VariablePattern _ _ v)       = do
  m <- getModuleIdent
  modifyValueEnv $ flip (bindVars m) [(v, 0, monoType ty)]
bindPatternVars _          (ConstructorPattern _ _ c ps) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (_, (tys, _)) <- liftM (fmap arrowUnapply) (inst (constrType m c vEnv))
  mapM_ (uncurry bindPatternVars) $ zip (map Check tys) ps
bindPatternVars cm         (InfixPattern _ a p1 op p2)
  = bindPatternVars cm (ConstructorPattern NoSpanInfo a op [p1, p2])
bindPatternVars cm         (ParenPattern _ p)            = bindPatternVars cm p
bindPatternVars _          (TuplePattern _ ps)
  = mapM_ (bindPatternVars Infer) ps
bindPatternVars _          (ListPattern _ _ ps)
  = mapM_ (bindPatternVars Infer) ps
bindPatternVars cm         (AsPattern _ v p)             = do
  bindPatternVars cm (VariablePattern undefined undefined v)
  bindPatternVars cm p
bindPatternVars cm         (LazyPattern _ p)             = bindPatternVars cm p
bindPatternVars _          (FunctionPattern _ _ f ps)    = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (_, (tys, _)) <- liftM (fmap arrowUnapply) (inst (funType m f vEnv))
  mapM_ (uncurry bindPatternVars) $ zip (map Check tys) ps
bindPatternVars cm         (InfixFuncPattern spi a p1 op p2)
  = bindPatternVars cm (FunctionPattern spi a op [p1, p2])
bindPatternVars _          (RecordPattern       _ _ _ fs) = do
  mapM_ bindFieldVars fs
bindPatternVars _ _ = ok

bindFieldVars :: Field (Pattern a) -> TCM ()
bindFieldVars (Field _ l p) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (_, ty) <- liftM (fmap arrowBase) (inst (labelType m l vEnv))
  bindPatternVars (Check ty) p

lambdaVar :: Ident -> TCM (Ident, Int, Type)
lambdaVar v = do
  ty <- freshTypeVar
  return (v, 0, monoType ty)

unifyDecl :: HasPosition p => p -> String -> Doc -> PredSet -> Type -> PredSet
          -> Type
          -> TCM PredSet
unifyDecl p what doc psLhs tyLhs psRhs tyRhs = do
  ps <- unify p what doc psLhs tyLhs psRhs tyRhs
  fvs <- computeFvEnv
  applyDefaultsDecl p what doc fvs ps tyLhs

-- After inferring types for a group of mutually recursive declarations
-- and computing the set of its constrained type variables, the compiler
-- has to be prepared for some of the constrained type variables to not
-- appear in some of the inferred types, i.e., there may be ambiguous
-- types that have not been reported by 'unifyDecl' above at the level
-- of individual function equations and pattern declarations.

defaultPDecl :: Set.Set Int -> PredSet -> Type -> PDecl a -> TCM PredSet
defaultPDecl fvs ps ty (_, FunctionDecl p _ f _) =
  applyDefaultsDecl p ("function " ++ escName f) empty fvs ps ty
defaultPDecl fvs ps ty (_, PatternDecl p t _) = case t of
  VariablePattern _ _ v ->
    applyDefaultsDecl p ("variable " ++ escName v) empty fvs ps ty
  _ -> return ps
defaultPDecl _ _ _ _ = internalError "TypeCheck.defaultPDecl"

applyDefaultsDecl :: HasPosition p => p -> String -> Doc -> Set.Set Int
                  -> PredSet -> Type -> TCM PredSet
applyDefaultsDecl p what doc fvs ps ty = do
  theta <- getTypeSubst
  let ty' = subst theta ty
      fvs' = foldr Set.insert fvs $ typeVars ty'
  applyDefaults p what doc fvs' ps ty'

-- After 'tcDeclGroup' has generalized the types of the implicitly
-- typed declarations of a declaration group it must update their left
-- hand side type annotations and the type environment accordingly.
-- Recall that the compiler generalizes only the types of variable and
-- function declarations.

fixType :: Type -> PDecl Type -> PDecl Type
fixType ~(TypeForall _ (TypeContext ps ty)) (i, FunctionDecl p _ f eqs) =
  (i, FunctionDecl p (TypeContext ps ty) f eqs)
fixType ~(TypeForall _ (TypeContext ps ty)) pd@(i, PatternDecl p t rhs) = case t of
  VariablePattern spi _ v
    -> (i, PatternDecl p (VariablePattern spi (TypeContext ps ty) v) rhs)
  _ -> pd
fixType _ _ = internalError "TypeCheck.fixType"

declVars :: Decl Type -> [(Ident, Int, Type)]
declVars (FunctionDecl _ pty f eqs) = [(f, eqnArity $ head eqs, typeScheme pty)]
declVars (PatternDecl _ t _) = case t of
  VariablePattern _ pty v -> [(v, 0, typeScheme pty)]
  _                       -> []
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

tcCheckPDecl :: PredSet -> TypeExpr -> PDecl a
             -> TCM (PredSet, PDecl Type)
tcCheckPDecl ps qty pd = do
  (ps', (ty, pd')) <- tcPDecl ps pd
  fvs <- computeFvEnv
  theta <- getTypeSubst
  poly <- isNonExpansive $ snd pd
  let (gps, lps) = splitPredSet fvs ps'
      ty' = subst theta ty
      tySc = if poly then gen fvs lps ty' else monoType ty'
  checkPDeclType qty gps tySc pd'

checkPDeclType :: TypeExpr -> PredSet -> Type -> PDecl Type
               -> TCM (PredSet, PDecl Type)
checkPDeclType qty ps tySc (i, FunctionDecl p _ f eqs) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral p m (text "Function:" <+> ppIdent f) qty
                                  (rawPredType tySc)
  return (ps, (i, FunctionDecl p pty f eqs))
checkPDeclType qty ps tySc (i, PatternDecl p (VariablePattern spi _ v) rhs) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral p m (text "Variable:" <+> ppIdent v) qty
                                  (rawPredType tySc)
  return (ps, (i, PatternDecl p (VariablePattern spi pty v) rhs))
checkPDeclType _ _ _ _ = internalError "TypeCheck.checkPDeclType"

checkTypeSig :: Type -> Type -> TCM Bool
checkTypeSig (TypeContext sigPs sigTy) (TypeForall _ (TypeContext ps ty)) = do
  clsEnv <- getClassEnv
  return $
    ty `eqTypes` sigTy &&
    all (`Set.member` maxPredSet clsEnv sigPs) (Set.toList ps)
checkTypeSig _ pty = internalError $ "Checks.TypeCheck.checkTypeSig: " ++ show pty

-- The function 'equTypes' computes whether two types are equal modulo
-- renaming of type variables.
-- WARNING: This operation is not reflexive and expects the second type to be
-- the type signature provided by the programmer.
eqTypes :: Type -> Type -> Bool
eqTypes t1 t2 = fst (eq [] t1 t2)
 where
 -- @is@ is an AssocList of type variable indices
 eq is (TypeConstructor   qid1) (TypeConstructor   qid2) = (qid1 == qid2, is)
 eq is (TypeVariable        i1) (TypeVariable        i2) = eqVar is i1 i2
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
   = let (res1, is') = eqs (eqUnbound is1 is) (map TypeVariable is1)
                                              (map TypeVariable is2)
         (res2, is'') = eq is' t1' t2'
     in  (res1 && res2, is ++ eqUnbound is1 is'')
 eq is (TypeContext ps1 t1') (TypeContext ps2 t2')
   = let ls1 = map (\(Pred c ty) -> TypeApply (TypeConstructor c) ty) (Set.toAscList ps1)
         ls2 = map (\(Pred c ty) -> TypeApply (TypeConstructor c) ty) (Set.toAscList ps2)
         (res1, is') = eqs is ls1 ls2
         (res2, is'') = eq is' t1' t2'
     in  (res1 && res2, is'')
 eq is _                        _                        = (False, is)

 eqUnbound tvs = filter (not . (`elem` tvs) . fst)

 eqVar is i1 i2 = case lookup i1 is of
   Nothing  -> (True, (i1, i2) : is)
   Just i2' -> (i2 == i2', is)

 eqs is []        []        = (True , is)
 eqs is (t1':ts1) (t2':ts2)
    = let (res1, is1) = eq  is t1'  t2'
          (res2, is2) = eqs is1 ts1 ts2
      in  (res1 && res2, is2)
 eqs is _         _         = (False, is)

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
  isNonExpansive (InfixDecl       _ _ _ _) = return True
  isNonExpansive (TypeSig           _ _ _) = return True
  isNonExpansive (FunctionDecl    _ _ _ _) = return True
  isNonExpansive (ExternalDecl        _ _) = return True
  isNonExpansive (PatternDecl       _ _ _) = return False
    -- TODO: Uncomment when polymorphic let declarations are fully supported
  {-isNonExpansive (PatternDecl     _ t rhs) = case t of
    VariablePattern _ _ -> isNonExpansive rhs
    _                   -> return False-}
  isNonExpansive (FreeDecl            _ _) = return False
  isNonExpansive _                         =
    internalError "TypeCheck.isNonExpansive: declaration"

instance Binding (Rhs a) where
  isNonExpansive (SimpleRhs _ e ds) = withLocalValueEnv $ do
    m <- getModuleIdent
    tcEnv <- getTyConsEnv
    clsEnv <- getClassEnv
    sigs <- getSigEnv
    modifyValueEnv $ flip (foldr (bindDeclArity m tcEnv clsEnv sigs)) ds
    isNonExpansive e &&^ isNonExpansive ds
  isNonExpansive (GuardedRhs _ _ _) = return False

-- A record construction is non-expansive only if all field labels are present.

instance Binding (Expression a) where
  isNonExpansive = isNonExpansive' 0

isNonExpansive' :: Int -> Expression a -> TCM Bool
isNonExpansive' _ (Literal         _ _ _) = return True
isNonExpansive' n (Variable        _ _ v)
  | v' == anonId = return False
  | isRenamed v' = do
    vEnv <- getValueEnv
    return $ n == 0 || n < varArity v vEnv
  | otherwise = do
    vEnv <- getValueEnv
    return $ n < varArity v vEnv
  where v' = unqualify v
isNonExpansive' _ (Constructor     _ _ _) = return True
isNonExpansive' n (Paren             _ e) = isNonExpansive' n e
isNonExpansive' n (Typed           _ e _) = isNonExpansive' n e
isNonExpansive' _ (Record       _ _ c fs) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  liftM ((length (constrLabels m c vEnv) == length fs) &&) (isNonExpansive fs)
isNonExpansive' _ (Tuple            _ es) = isNonExpansive es
isNonExpansive' _ (List           _ _ es) = isNonExpansive es
isNonExpansive' n (Apply           _ f e) =
  isNonExpansive' (n + 1) f &&^ isNonExpansive e
isNonExpansive' n (InfixApply _ e1 op e2) =
  isNonExpansive' (n + 2) (infixOp op) &&^ isNonExpansive e1 &&^
    isNonExpansive e2
isNonExpansive' n (LeftSection    _ e op) =
  isNonExpansive' (n + 1) (infixOp op) &&^ isNonExpansive e
isNonExpansive' n (Lambda         _ ts e) = withLocalValueEnv $ do
  modifyValueEnv $ flip (foldr bindVarArity) (bv ts)
  liftM ((n < length ts) ||)
    (liftM ((all isVariablePattern ts) &&) (isNonExpansive' (n - length ts) e))
isNonExpansive' n (Let            _ ds e) = withLocalValueEnv $ do
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
bindDeclArity _ _     _      _    (InfixDecl        _ _ _ _) = id
bindDeclArity _ _     _      _    (TypeSig            _ _ _) = id
bindDeclArity _ _     _      _    (FunctionDecl   _ _ f eqs) =
  bindArity f (eqnArity $ head eqs)
bindDeclArity m tcEnv clsEnv sigs (ExternalDecl        _ fs) =
  flip (foldr $ \(Var _ f) -> bindArity f $ arrowArity $ ty f) fs
  where ty = unpredType . expandPolyType m tcEnv clsEnv . fromJust .
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
bindArity v n = bindTopEnv v (Value (qualify v) False n undefined)

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
-- When checking inferred method types against their expected types, we
-- have to be careful because the class' type variable is always assigned
-- index 0 in the method types recorded in the value environment. However,
-- in the inferred type scheme returned from 'tcMethodDecl', type variables
-- are assigned indices in the order of their occurrence. In order to avoid
-- incorrectly reporting errors when the type class variable is not the first
-- variable that appears in a method's type, 'tcInstMethodDecl' normalizes
-- the expected method type before applying 'checkInstMethodType' to it and
-- 'checkClassMethodType' uses 'expandPolyType' instead of 'expandMethodType'
-- in order to convert the method's type signature. Unfortunately, this means
-- that the compiler has to add the class constraint explicitly to the type
-- signature.

tcTopPDecl :: PDecl a -> TCM (PDecl Type)
tcTopPDecl (i, DataDecl p tc tvs cs clss) =
  return (i, DataDecl p tc tvs cs clss)
tcTopPDecl (i, ExternalDataDecl p tc tvs) =
  return (i, ExternalDataDecl p tc tvs)
tcTopPDecl (i, NewtypeDecl p tc tvs nc clss) =
  return (i, NewtypeDecl p tc tvs nc clss)
tcTopPDecl (i, TypeDecl p tc tvs ty) = return (i, TypeDecl p tc tvs ty)
tcTopPDecl (i, DefaultDecl p tys) = return (i, DefaultDecl p tys)
tcTopPDecl (i, ClassDecl p cx cls tv ds) = withLocalSigEnv $ do
  setSigEnv $ foldr (bindTypeSigs . snd) emptySigEnv opds
  vpds' <- mapM (tcClassMethodPDecl (qualify cls) tv) vpds
  return (i, ClassDecl p cx cls tv $ fromPDecls $ map untyped opds ++ vpds')
  where (vpds, opds) = partition (isValueDecl . snd) $ toPDecls ds
tcTopPDecl (i, InstanceDecl p cx qcls ty ds) = do
  tcEnv <- getTyConsEnv
  pty <- expandPoly $ ContextType NoSpanInfo cx ty
  mid <- getModuleIdent
  let origCls = getOrigName mid qcls tcEnv
      clsQual = head $ filter isQualified $ reverseLookupByOrigName origCls tcEnv
      qQualCls = qualQualify (fromJust $ qidModule clsQual) qcls
  vpds' <- mapM (tcInstanceMethodPDecl qQualCls pty) vpds
  return (i, InstanceDecl p cx qcls ty $ fromPDecls $ map untyped opds ++ vpds')
  where (vpds, opds) = partition (isValueDecl . snd) $ toPDecls ds
tcTopPDecl _ = internalError "Checks.TypeCheck.tcTopDecl"

tcClassMethodPDecl :: QualIdent -> Ident -> PDecl a -> TCM (PDecl Type)
tcClassMethodPDecl qcls tv pd@(_, FunctionDecl _ _ f _) = do
  methTy <- classMethodType qualify f
  (tySc, pd') <- tcMethodPDecl methTy pd
  sigs <- getSigEnv
  let qty = toClassMethodTypeExpr qcls tv $ fromJust $ lookupTypeSig f sigs
  checkClassMethodType qty tySc pd'
tcClassMethodPDecl _ _ _ = internalError "TypeCheck.tcClassMethodPDecl"

toClassMethodTypeExpr :: QualIdent -> Ident -> TypeExpr -> TypeExpr
toClassMethodTypeExpr qcls clsvar (ContextType spi cx ty)
  = ContextType spi (Constraint NoSpanInfo qcls (VariableType NoSpanInfo clsvar) : cx) ty
toClassMethodTypeExpr qcls clsvar ty
  = ContextType NoSpanInfo [Constraint NoSpanInfo qcls (VariableType NoSpanInfo clsvar)] ty

tcInstanceMethodPDecl :: QualIdent -> Type -> PDecl a -> TCM (PDecl Type)
tcInstanceMethodPDecl qcls pty pd@(_, FunctionDecl _ _ f _) = do
  methTy <- instMethodType (qualifyLike qcls) pty f
  (tySc, pd') <- tcMethodPDecl (typeScheme methTy) pd
  checkInstMethodType (normalize 0 methTy) tySc pd'
tcInstanceMethodPDecl _ _ _ = internalError "TypeCheck.tcInstanceMethodPDecl"

tcMethodPDecl :: Type -> PDecl a -> TCM (Type, PDecl Type)
tcMethodPDecl tySc (i, FunctionDecl p _ f eqs) = withLocalValueEnv $ do
  m <- getModuleIdent
  modifyValueEnv $ bindFun m f True (eqnArity $ head eqs) tySc
  (ps, (ty, pd)) <- tcFunctionPDecl i emptyPredSet tySc p f eqs
  theta <- getTypeSubst
  return (gen Set.empty ps $ subst theta ty, pd)
tcMethodPDecl _ _ = internalError "TypeCheck.tcMethodPDecl"

checkClassMethodType :: TypeExpr -> Type -> PDecl Type
                     -> TCM (PDecl Type)
checkClassMethodType qty tySc pd@(_, FunctionDecl p _ f _) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral p m (text "Method:" <+> ppIdent f) qty
                                  (rawPredType tySc)
  return pd
checkClassMethodType _ _ _ = internalError "TypeCheck.checkClassMethodType"

checkInstMethodType :: Type -> Type -> PDecl Type -> TCM (PDecl Type)
checkInstMethodType pty tySc pd@(_, FunctionDecl p _ f _) = do
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $
      errMethodTypeTooSpecific p m (text "Method:" <+> ppIdent f) pty
                               (rawPredType tySc)
  return pd
checkInstMethodType _ _ _ = internalError "TypeCheck.checkInstMethodType"

classMethodType :: (Ident -> QualIdent) -> Ident -> TCM Type
classMethodType qual f = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  return $ funType m (qual $ unRenameIdent f) vEnv

-- Due to the sorting of the predicate set, we can simply remove the minimum
-- element as this is guaranteed to be the class constraint (see module 'Types'
-- for more information).

instMethodType :: (Ident -> QualIdent) -> Type -> Ident -> TCM Type
instMethodType qual (TypeContext ps ty) f = do
  tySc <- classMethodType qual f
  let TypeForall _ (TypeContext ps' _) = tySc
      TypeContext ps'' ty'' = instanceType ty (TypeContext (Set.deleteMin ps') (rawType tySc))
  return $ TypeContext (ps `Set.union` ps'') ty''
instMethodType _ _ _ = internalError "TypeCheck.instMethodType"

-- External functions:

tcExternal :: Ident -> TCM Type
tcExternal f = do
  sigs <- getSigEnv
  case lookupTypeSig f sigs of
    Nothing -> internalError "TypeCheck.tcExternal: type signature not found"
    Just ty -> do
      m <- getModuleIdent
      ty' <- unpredType <$> (expandPoly $ createContext ty)
      modifyValueEnv $ bindFun m f False (arrowArity ty') (polyType ty')
      return ty'
  where
    createContext (ContextType _ _ ty) = ContextType NoSpanInfo [] ty
    createContext ty                   = ContextType NoSpanInfo [] ty

-- Patterns and Expressions:
-- Note that the type attribute associated with a constructor or infix
-- pattern is the type of the whole pattern and not the type of the
-- constructor itself. Overloaded (numeric) literals are not supported in
-- patterns.

tcLiteral :: Bool -> Literal -> TCM (PredSet, Type)
tcLiteral _    (Char _)   = return (emptyPredSet, charType)
tcLiteral poly (Int _)
  | poly      = freshNumType
  | otherwise = liftM ((,) emptyPredSet) (freshConstrained numTypes)
tcLiteral poly (Float _)
  | poly      = freshFractionalType
  | otherwise = liftM ((,) emptyPredSet) (freshConstrained fractionalTypes)
tcLiteral _    (String _) = return (emptyPredSet, stringType)

tcLhs :: HasPosition p => p -> Lhs a -> TCM (PredSet, [Type], Lhs Type)
tcLhs p (FunLhs spi f ts) = do
  (pss, tys, ts') <- liftM unzip3 $ mapM (tcPattern p) ts
  return (Set.unions pss, tys, FunLhs spi f ts')
tcLhs p (OpLhs spi t1 op t2) = do
  (ps1, ty1, t1') <- tcPattern p t1
  (ps2, ty2, t2') <- tcPattern p t2
  return (ps1 `Set.union` ps2, [ty1, ty2], OpLhs spi t1' op t2')
tcLhs p (ApLhs spi lhs ts) = do
  (ps, tys1, lhs') <- tcLhs p lhs
  (pss, tys2, ts') <- liftM unzip3 $ mapM (tcPattern p) ts
  return (Set.unions (ps:pss), tys1 ++ tys2, ApLhs spi lhs' ts')

-- When computing the type of a variable in a pattern, we ignore the
-- predicate set of the variable's type (which can only be due to a type
-- signature in the same declaration group) for just the same reason as
-- in 'tcFunctionPDecl'. Infix and infix functional patterns are currently
-- checked as constructor and functional patterns, respectively, resulting
-- in slighty misleading error messages if the type check fails.

tcPattern :: HasPosition p => p -> Pattern a
          -> TCM (PredSet, Type, Pattern Type)
tcPattern _ (LiteralPattern spi _ l) = do
  (ps, ty) <- tcLiteral False l
  return (ps, ty, LiteralPattern spi (predType ty) l)
tcPattern _ (NegativePattern spi _ l) = do
  (ps, ty) <- tcLiteral False l
  return (ps, ty, NegativePattern spi (predType ty) l)
tcPattern _ (VariablePattern spi _ v) = do
  vEnv <- getValueEnv
  (_, ty) <- inst (varType v vEnv)
  return (emptyPredSet, ty, VariablePattern spi (predType ty) v)
tcPattern p t@(ConstructorPattern spi _ c ts) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, (tys, ty')) <- liftM (fmap arrowUnapply) (inst (constrType m c vEnv))
  (ps', ts') <- mapAccumM (uncurry . tcPatternArg p "pattern" (ppPattern 0 t))
                          ps (zip tys ts)
  return (ps', ty', ConstructorPattern spi (predType ty') c ts')
tcPattern p (InfixPattern spi a t1 op t2) = do
  (ps, ty, t') <- tcPattern p (ConstructorPattern NoSpanInfo a op [t1, t2])
  let ConstructorPattern _ a' op' [t1', t2'] = t'
  return (ps, ty, InfixPattern spi a' t1' op' t2')
tcPattern p (ParenPattern spi t) = do
  (ps, ty, t') <- tcPattern p t
  return (ps, ty, ParenPattern spi t')
tcPattern _ t@(RecordPattern spi _ c fs) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- liftM (fmap arrowBase) (inst (constrType m c vEnv))
  (ps', fs') <- mapAccumM (tcField tcPattern "pattern"
    (\t' -> ppPattern 0 t $-$ text "Term:" <+> ppPattern 0 t') ty) ps fs
  return (ps', ty, RecordPattern spi (predType ty) c fs')
tcPattern p (TuplePattern spi ts) = do
  (pss, tys, ts') <- liftM unzip3 $ mapM (tcPattern p) ts
  return (Set.unions pss, tupleType tys, TuplePattern spi ts')
tcPattern p t@(ListPattern spi _ ts) = do
  ty <- freshTypeVar
  (ps, ts') <- mapAccumM (flip (tcPatternArg p "pattern" (ppPattern 0 t)) ty)
                         emptyPredSet ts
  return (ps, listType ty, ListPattern spi (predType $ listType ty) ts')
tcPattern p t@(AsPattern spi v t') = do
  vEnv <- getValueEnv
  (_, ty) <- inst (varType v vEnv)
  (ps, t'') <- tcPattern p t' >>-
    unify p "pattern" (ppPattern 0 t) emptyPredSet ty
  return (ps, ty, AsPattern spi v t'')
tcPattern p (LazyPattern spi t) = do
  (ps, ty, t') <- tcPattern p t
  return (ps, ty, LazyPattern spi t')
tcPattern p t@(FunctionPattern spi _ f ts) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- inst (funType m f vEnv)
  tcFuncPattern p spi (ppPattern 0 t) f id ps ty ts
tcPattern p (InfixFuncPattern spi a t1 op t2) = do
  (ps, ty, t') <- tcPattern p (FunctionPattern spi a op [t1, t2])
  let FunctionPattern _ a' op' [t1', t2'] = t'
  return (ps, ty, InfixFuncPattern spi a' t1' op' t2')

tcFuncPattern :: HasPosition p => p -> SpanInfo -> Doc -> QualIdent
              -> ([Pattern Type] -> [Pattern Type])
              -> PredSet -> Type -> [Pattern a]
              -> TCM (PredSet, Type, Pattern Type)
tcFuncPattern _ spi _ f ts ps ty [] =
  return (ps, ty, FunctionPattern spi (predType ty) f (ts []))
tcFuncPattern p spi doc f ts ps ty (t':ts') = do
  (alpha, beta) <-
    tcArrow p "functional pattern" (doc $-$ text "Term:" <+> ppPattern 0 t) ty
  (ps', t'') <- tcPatternArg p "functional pattern" doc ps alpha t'
  tcFuncPattern p spi doc f (ts . (t'' :)) ps' beta ts'
  where t = FunctionPattern spi (predType ty) f (ts [])

tcPatternArg :: HasPosition p => p -> String -> Doc -> PredSet -> Type
             -> Pattern a -> TCM (PredSet, Pattern Type)
tcPatternArg p what doc ps ty t =
  tcPattern p t >>-
    unify p what (doc $-$ text "Term:" <+> ppPattern 0 t) ps ty

tcRhs :: CheckMode -> Rhs a -> TCM (PredSet, Type, Rhs Type)
tcRhs cm (SimpleRhs p e ds) = do
  (ps, ds', ps', ty, e') <- withLocalValueEnv $ do
    (ps, ds') <- tcDecls ds
    (ps', ty, e') <- tcExpr cm p e
    return (ps, ds', ps', ty, e')
  ps'' <- reducePredSet p "expression" (ppExpr 0 e') (ps `Set.union` ps')
  return (ps'', ty, SimpleRhs p e' ds')
tcRhs cm (GuardedRhs spi es ds) = withLocalValueEnv $ do
  (ps, ds') <- tcDecls ds
  ty <- freshTypeVar
  (ps', es') <- mapAccumM (tcCondExpr cm ty) ps es
  return (ps', ty, GuardedRhs spi es' ds')

tcCondExpr :: CheckMode -> Type -> PredSet -> CondExpr a -> TCM (PredSet, CondExpr Type)
tcCondExpr cm ty ps (CondExpr p g e) = do
  (ps', g') <- tcExpr Infer p g >>- unify p "guard" (ppExpr 0 g) ps boolType
  (ps'', e') <- tcExpr cm p e >>- unify p "guarded expression" (ppExpr 0 e) ps' ty
  return (ps'', CondExpr p g' e')

tcExpr :: HasPosition p => CheckMode -> p -> Expression a
       -> TCM (PredSet, Type, Expression Type)
tcExpr _     _ (Literal spi _ l) = do
  (ps, ty) <- tcLiteral True l
  return (ps, ty, Literal spi (predType ty) l)
tcExpr _     _ (Variable spi _ v) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- if isAnonId (unqualify v) then freshPredType []
                                        else inst (funType m v vEnv)
  return (ps, ty, Variable spi (predType ty) v)
tcExpr _     _ (Constructor spi _ c) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- inst (constrType m c vEnv)
  return (ps, ty, Constructor spi (predType ty) c)
tcExpr cm    p (Paren spi e) = do
  (ps, ty, e') <- tcExpr cm p e
  return (ps, ty, Paren spi e')
tcExpr _     p (Typed spi e qty) = do
  pty <- expandPoly qty
  (ps, ty) <- inst (typeScheme pty)
  (ps', e') <- tcExpr (Check ty) p e >>-
    unifyDecl p "explicitly typed expression" (ppExpr 0 e) emptyPredSet ty
  fvs <- computeFvEnv
  theta <- getTypeSubst
  let (gps, lps) = splitPredSet fvs ps'
      tySc = gen fvs lps (subst theta ty)
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $
      errTypeSigTooGeneral p m (text "Expression:" <+> ppExpr 0 e) qty
                           (rawPredType tySc)
  return (ps `Set.union` gps, ty, Typed spi e' qty)
tcExpr _     _ e@(Record spi _ c fs) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- liftM (fmap arrowBase) (inst (constrType m c vEnv))
  (ps', fs') <- mapAccumM (tcField (tcExpr Infer) "construction"
    (\e' -> ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e') ty) ps fs
  return (ps', ty, Record spi (predType ty) c fs')
tcExpr _     p e@(RecordUpdate spi e1 fs) = do
  (ps, ty, e1') <- tcExpr Infer p e1
  (ps', fs') <- mapAccumM (tcField (tcExpr Infer) "update"
    (\e' -> ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e') ty) ps fs
  return (ps', ty, RecordUpdate spi e1' fs')
tcExpr _     p (Tuple spi es) = do
  (pss, tys, es') <- liftM unzip3 $ mapM (tcExpr Infer p) es
  return (Set.unions pss, tupleType tys, Tuple spi es')
tcExpr _     p e@(List spi _ es) = do
  ty <- freshTypeVar
  (ps, es') <-
    mapAccumM (flip (tcArg Infer p "expression" (ppExpr 0 e)) ty) emptyPredSet es
  return (ps, listType ty, List spi (predType $ listType ty) es')
tcExpr _     p (ListCompr spi e qs) = do
  (ps, qs', ps', ty, e') <- withLocalValueEnv $ do
    (ps, qs') <- mapAccumM (tcQual p) emptyPredSet qs
    (ps', ty, e') <- tcExpr Infer p e
    return (ps, qs', ps', ty, e')
  ps'' <- reducePredSet p "expression" (ppExpr 0 e') (ps `Set.union` ps')
  return (ps'', listType ty, ListCompr spi e' qs')
tcExpr _     p e@(EnumFrom spi e1) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  return (ps', listType ty, EnumFrom spi e1')
tcExpr _     p e@(EnumFromThen spi e1 e2) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  (ps'', e2') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps' ty e2
  return (ps'', listType ty, EnumFromThen spi e1' e2')
tcExpr _     p e@(EnumFromTo spi e1 e2) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  (ps'', e2') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps' ty e2
  return (ps'', listType ty, EnumFromTo spi e1' e2')
tcExpr _     p e@(EnumFromThenTo spi e1 e2 e3) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  (ps'', e2') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps' ty e2
  (ps''', e3') <- tcArg Infer p "arithmetic sequence" (ppExpr 0 e) ps'' ty e3
  return (ps''', listType ty, EnumFromThenTo spi e1' e2' e3')
tcExpr _     p e@(UnaryMinus spi e1) = do
  (ps, ty) <- freshNumType
  (ps', e1') <- tcArg Infer p "unary negation" (ppExpr 0 e) ps ty e1
  return (ps', ty, UnaryMinus spi e1')
tcExpr _     p e@(Apply spi e1 e2) = do
  (ps, y, e1') <- tcExpr Infer p e1
  (ps', y') <- skolemise y
  (alpha, beta) <- tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) y'
  (ps'', e2') <- tcArg Infer p "application" (ppExpr 0 e) (ps `Set.union` ps') alpha e2
  return (ps'', beta, Apply spi e1' e2')
tcExpr _     p e@(InfixApply spi e1 op e2) = do
  (ps, (alpha, beta, gamma), op') <- tcInfixOp op >>=-
    tcBinary p "infix application" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
  (aps, alpha') <- skolemise alpha
  (ps', e1') <- tcArg Infer p "infix application" (ppExpr 0 e) (ps `Set.union` aps) alpha' e1
  (bps, beta') <- skolemise beta
  (ps'', e2') <- tcArg Infer p "infix application" (ppExpr 0 e) (ps' `Set.union` bps) beta' e2
  return (ps'', gamma, InfixApply spi e1' op' e2')
tcExpr _     p e@(LeftSection spi e1 op) = do
  (ps, (alpha, beta), op') <- tcInfixOp op >>=-
    tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
  (aps, alpha') <- skolemise alpha
  (ps', e1') <- tcArg Infer p "left section" (ppExpr 0 e) (ps `Set.union` aps) alpha e1
  return (ps', beta, LeftSection spi e1' op')
tcExpr _     p e@(RightSection spi op e1) = do
  (ps, (alpha, beta, gamma), op') <- tcInfixOp op >>=-
    tcBinary p "right section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
  (bps, beta') <- skolemise beta
  (ps', e1') <- tcArg Infer p "right section" (ppExpr 0 e) (ps `Set.union` bps) beta e1
  return (ps', TypeArrow alpha gamma, RightSection spi op' e1')
tcExpr cm    p (Lambda spi ts e) = do
  (pss, tys, ts', ps, ty, e') <- withLocalValueEnv $ do
    let cmList = (case cm of
                    Infer    -> map (const Infer) [0..]
                    Check ty -> let (argTys, _) = arrowUnapply ty
                                 in map Check argTys ++ map (const Infer) [0..])
    mapM_ (uncurry bindPatternVars) $ zip cmList ts
    (pss, tys, ts') <- liftM unzip3 $ mapM (tcPattern p) ts
    (ps, ty, e') <- tcExpr Infer p e
    return (pss, tys, ts', ps, ty, e')
  ps' <- reducePredSet p "expression" (ppExpr 0 e') (Set.unions $ ps : pss)
  return (ps', foldr TypeArrow ty tys, Lambda spi ts' e')
tcExpr cm    p (Let spi ds e) = do
  (ps, ds', ps', ty, e') <- withLocalValueEnv $ do
    (ps, ds') <- tcDecls ds
    (ps', ty, e') <- tcExpr cm p e
    return (ps, ds', ps', ty, e')
  ps'' <- reducePredSet p "expression" (ppExpr 0 e') (ps `Set.union` ps')
  return (ps'', ty, Let spi ds' e')
tcExpr _     p (Do spi sts e) = do
  (sts', ty, ps', e') <- withLocalValueEnv $ do
    ((ps, mTy), sts') <-
      mapAccumM (uncurry (tcStmt p)) (emptyPredSet, Nothing) sts
    ty <- liftM (maybe id TypeApply mTy) freshTypeVar
    (ps', e') <- tcExpr Infer p e >>- unify p "statement" (ppExpr 0 e) ps ty
    return (sts', ty, ps', e')
  return (ps', ty, Do spi sts' e')
tcExpr cm    p e@(IfThenElse spi e1 e2 e3) = do
  (ps, e1') <- tcArg Infer p "expression" (ppExpr 0 e) emptyPredSet boolType e1
  (ps', ty, e2') <- tcExpr cm p e2
  (ps'', e3') <- tcArg cm p "expression" (ppExpr 0 e) (ps `Set.union` ps') ty e3
  return (ps'', ty, IfThenElse spi e1' e2' e3')
tcExpr cm    p (Case spi ct e as) = do
  (ps, tyLhs, e') <- tcExpr Infer p e
  tyRhs <- freshTypeVar
  (ps', as') <- mapAccumM (tcAlt cm tyLhs tyRhs) ps as
  return (ps', tyRhs, Case spi ct e' as')

tcArg :: HasPosition p => CheckMode -> p -> String -> Doc -> PredSet -> Type
      -> Expression a -> TCM (PredSet, Expression Type)
tcArg cm p what doc ps ty e =
  tcExpr cm p e >>- unify p what (doc $-$ text "Term:" <+> ppExpr 0 e) ps ty

tcAlt :: CheckMode -> Type -> Type -> PredSet -> Alt a
      -> TCM (PredSet, Alt Type)
tcAlt cm tyLhs tyRhs ps a@(Alt p t rhs) =
  tcAltern cm tyLhs p t rhs >>-
    unify p "case alternative" (ppAlt a) ps tyRhs

tcAltern :: CheckMode -> Type -> SpanInfo -> Pattern a
         -> Rhs a -> TCM (PredSet, Type, Alt Type)
tcAltern cm tyLhs p t rhs = do
  (ps, t', ps', ty', rhs') <- withLocalValueEnv $ do
    bindPatternVars (Check tyLhs) t
    (ps, t') <-
      tcPatternArg p "case pattern" (ppAlt (Alt p t rhs)) emptyPredSet tyLhs t
    (ps', ty', rhs') <- tcRhs cm rhs
    return (ps, t', ps', ty', rhs')
  ps'' <- reducePredSet p "alternative" (ppAlt (Alt p t' rhs'))
                        (ps `Set.union` ps')
  return (ps'', ty', Alt p t' rhs')

tcQual :: HasPosition p => p -> PredSet -> Statement a
       -> TCM (PredSet, Statement Type)
tcQual p ps (StmtExpr spi e) = do
  (ps', e') <- tcExpr Infer p e >>- unify p "guard" (ppExpr 0 e) ps boolType
  return (ps', StmtExpr spi e')
tcQual _ ps (StmtDecl spi ds) = do
  (ps', ds') <- tcDecls ds
  return (ps `Set.union` ps', StmtDecl spi ds')
tcQual p ps q@(StmtBind spi t e) = do
  alpha <- freshTypeVar
  (ps', e') <- tcArg Infer p "generator" (ppStmt q) ps (listType alpha) e
  bindPatternVars Infer t
  (ps'', t') <- tcPatternArg p "generator" (ppStmt q) ps' alpha t
  return (ps'', StmtBind spi t' e')

tcStmt :: HasPosition p => p -> PredSet -> Maybe Type -> Statement a
       -> TCM ((PredSet, Maybe Type), Statement Type)
tcStmt p ps mTy (StmtExpr spi e) = do
  (ps', ty) <- maybe freshMonadType (return . (,) emptyPredSet) mTy
  alpha <- freshTypeVar
  (ps'', e') <- tcExpr Infer p e >>-
    unify p "statement" (ppExpr 0 e) (ps `Set.union` ps') (applyType ty [alpha])
  return ((ps'', Just ty), StmtExpr spi e')
tcStmt _ ps mTy (StmtDecl spi ds) = do
  (ps', ds') <- tcDecls ds
  return ((ps `Set.union` ps', mTy), StmtDecl spi ds')
tcStmt p ps mTy st@(StmtBind spi t e) = do
  (ps', ty) <- maybe freshMonadType (return . (,) emptyPredSet) mTy
  alpha <- freshTypeVar
  (ps'', e') <-
    tcArg Infer p "statement" (ppStmt st) (ps `Set.union` ps') (applyType ty [alpha]) e
  bindPatternVars Infer t
  (ps''', t') <- tcPatternArg p "statement" (ppStmt st) ps'' alpha t
  return ((ps''', Just ty), StmtBind spi t' e')

tcInfixOp :: InfixOp a -> TCM (PredSet, Type, InfixOp Type)
tcInfixOp (InfixOp _ op) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- inst (funType m op vEnv)
  return (ps, ty, InfixOp (predType ty) op)
tcInfixOp (InfixConstr _ op) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- inst (constrType m op vEnv)
  return (ps, ty, InfixConstr (predType ty) op)

-- The first unification in 'tcField' cannot fail; it serves only for
-- instantiating the type variables in the field label's type.

tcField :: (Position -> a b -> TCM (PredSet, Type, a Type))
        -> String -> (a b -> Doc) -> Type -> PredSet -> Field (a b)
        -> TCM (PredSet, Field (a Type))
tcField check what doc ty ps (Field p l x) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps', ty') <- inst (labelType m l vEnv)
  let TypeArrow ty1 ty2 = ty'
  _ <- unify p "field label" empty emptyPredSet ty emptyPredSet ty1
  (ps'', x') <- check (spanInfo2Pos p) x >>-
    unify p ("record " ++ what) (doc x) (ps `Set.union` ps') ty2
  return (ps'', Field p l x')

-- | Checks that its argument can be used as an arrow type @a -> b@ and returns
-- the pair @(a, b)@.
tcArrow :: HasPosition p => p -> String -> Doc -> Type -> TCM (Type, Type)
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

-- | Checks that its argument can be used as an arrow type @a -> b -> c@ and
-- returns the triple @(a, b, c)@.
tcBinary :: HasPosition p => p -> String -> Doc -> Type
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
    (,,) <$> return ty1 <*> freshTypeVar <*> freshTypeVar

-- -----------------------------------------------------------------------------
-- Unification (Robinson's algorithm)
-- -----------------------------------------------------------------------------

unify :: HasPosition p => p -> String -> Doc -> PredSet -> Type -> PredSet
      -> Type -> TCM PredSet
unify p what doc ps1 ty1 ps2 ty2 = do
  theta <- getTypeSubst
  let ty1' = subst theta ty1
      ty2' = subst theta ty2
  m <- getModuleIdent
  res <- unifyTypes m ty1' ty2'
  let ps = either (const emptyPredSet) fst res
  case res of
    Left reason      -> report $ errTypeMismatch p what doc m ty1' ty2' reason
    Right (_, sigma) -> modifyTypeSubst (compose sigma)
  _ <- reducePredSet p what doc ps
  reducePredSet p what doc $ (ps1 `Set.union` ps2)

unifyTypes :: ModuleIdent -> Type -> Type
           -> TCM (Either Doc (PredSet, TypeSubst))
unifyTypes _ (TypeVariable tv1)         ty@(TypeVariable tv2)
  | tv1 == tv2 = return $ Right (emptyPredSet, idSubst)
  | otherwise  = return $ Right (emptyPredSet, singleSubst tv1 ty)
unifyTypes m (TypeVariable tv)          ty
  | tv `elem` typeVars ty = return $ Left (errRecursiveType m tv ty)
  | otherwise             = return $ Right (emptyPredSet, singleSubst tv ty)
unifyTypes m ty                         (TypeVariable tv)
  | tv `elem` typeVars ty = return $ Left (errRecursiveType m tv ty)
  | otherwise             = return $ Right (emptyPredSet, singleSubst tv ty)
unifyTypes _ (TypeConstrained tys1 tv1) ty@(TypeConstrained tys2 tv2)
  | tv1 == tv2   = return $ Right (emptyPredSet, idSubst)
  | tys1 == tys2 = return $ Right (emptyPredSet, singleSubst tv1 ty)
unifyTypes m (TypeConstrained tys tv)   ty
  = foldrM (\ty' s -> liftM (`choose` s) (unifyTypes m ty ty'))
           (Left (errIncompatibleTypes m ty (head tys)))
           tys
  where
    choose (Left _)            theta' = theta'
    choose (Right (ps, theta)) _      = Right (ps, bindSubst tv ty theta)
unifyTypes m ty                         (TypeConstrained tys tv)
  = foldrM (\ty' s -> liftM (`choose` s) (unifyTypes m ty ty'))
           (Left (errIncompatibleTypes m ty (head tys)))
           tys
  where
    choose (Left _)            theta' = theta'
    choose (Right (ps, theta)) _      = Right (ps, bindSubst tv ty theta)
unifyTypes _ (TypeConstructor tc1)      (TypeConstructor tc2)
  | tc1 == tc2 = return $ Right (emptyPredSet, idSubst)
unifyTypes m (TypeApply ty11 ty12)      (TypeApply ty21 ty22)
  = unifyTypeLists m [ty11, ty12] [ty21, ty22]
unifyTypes m ty@(TypeApply _ _)         (TypeArrow ty21 ty22)
  = unifyTypes m ty (TypeApply (TypeApply (TypeConstructor qArrowId) ty21) ty22)
unifyTypes m (TypeArrow ty11 ty12)      ty@(TypeApply _ _)
  = unifyTypes m (TypeApply (TypeApply (TypeConstructor qArrowId) ty11) ty12) ty
unifyTypes m (TypeArrow ty11 ty12)      (TypeArrow ty21 ty22)
  = unifyTypeLists m [ty11, ty12] [ty21, ty22]
unifyTypes m ty1@(TypeForall _ _)       ty2@(TypeForall _ _)
  = do (ps1, ty1') <- skolemise ty1
       (ps2, ty2') <- skolemise ty2
       res <- unifyTypes m ty1' ty2'
       let ps = ps1 `Set.union` ps2
       case res of
         Left x         -> return $ Left x
         Right (ps', s) -> return $ Right (ps `Set.union` ps', s)
unifyTypes m ty1@(TypeForall _ _)       ty2
  = do (ps1, ty1') <- skolemise ty1
       res <- unifyTypes m ty1' ty2
       case res of
         Left x        -> return $ Left x
         Right (ps, s) -> return $ Right (ps1 `Set.union` ps, s)
unifyTypes m ty1                        ty2@(TypeForall _ _)
  = do (ps2, ty2') <- skolemise ty2
       res <- unifyTypes m ty1 ty2'
       case res of
         Left x        -> return $ Left x
         Right (ps, s) -> return $ Right (ps2 `Set.union` ps, s)
unifyTypes m ty1                        ty2
  = return $ Left (errIncompatibleTypes m ty1 ty2)

unifyTypeLists :: ModuleIdent -> [Type] -> [Type]
               -> TCM (Either Doc (PredSet, TypeSubst))
unifyTypeLists _ []         _          = return $ Right (emptyPredSet, idSubst)
unifyTypeLists _ _          []         = return $ Right (emptyPredSet, idSubst)
unifyTypeLists m (ty1:tys1) (ty2:tys2) = do
  res <- unifyTypeLists m tys1 tys2
  case res of
    Left x        -> return $ Left x
    Right (ps, s) -> unifyTypesTheta ps s
  where
    unifyTypesTheta ps theta = do
      res <- unifyTypes m (subst theta ty1) (subst theta ty2)
      case res of
        Left x        -> return $ Left x
        Right (ps', s) -> return $ Right (ps `Set.union` ps', compose s theta)

-- After performing a unification, the resulting substitution is applied to the
-- current predicate set and the resulting predicate set is subject to a
-- reduction. This predicate set reduction retains all predicates whose types
-- are simple variables and which are not implied by other predicates in the
-- predicate set. For all other predicates, the compiler checks whether an
-- instance exists and replaces them by applying the instances' predicate set
-- to the respective types. A minor complication arises due to constrained
-- types, which at present are used to implement overloading of guard
-- expressions and of numeric literals in patterns. The set of admissible types
-- of a constrained type may be restricted by the current predicate set after
-- the reduction and thus may cause a further extension of the current type
-- substitution.

reducePredSet :: HasPosition p => p -> String -> Doc -> PredSet -> TCM PredSet
reducePredSet p what doc ps = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  theta <- getTypeSubst
  inEnv <- (fmap $ fmap $ subst theta) <$> getInstEnv
  let ps' = subst theta ps
      (ps1, ps2) = partitionPredSet $ minPredSet clsEnv $ reducePreds inEnv ps'
  theta' <- foldM (reportMissingInstance m p what doc inEnv) idSubst
                  (Set.toList ps2)
  modifyTypeSubst $ compose theta'
  return ps1
  where
    reducePreds inEnv = Set.concatMap $ reducePred inEnv
    reducePred inEnv pr@(Pred qcls ty) = maybe (Set.singleton pr)
                                               (reducePreds inEnv)
                                               (instPredSet inEnv qcls ty)

instPredSet :: InstEnv' -> QualIdent -> Type -> Maybe PredSet
instPredSet inEnv qcls ty = case Map.lookup qcls $ snd inEnv of
  Just tys | ty `elem` tys -> Just emptyPredSet
  _                        -> case unapplyType False ty of
    (TypeConstructor tc, tys) -> fmap (expandAliasType tys . snd3)
                                      (lookupInstInfo (qcls, tc) $ fst inEnv)
    _                         -> Nothing

reportMissingInstance :: HasPosition p => ModuleIdent -> p -> String -> Doc
                      -> InstEnv' -> TypeSubst -> Pred -> TCM TypeSubst
reportMissingInstance m p what doc inEnv theta (Pred qcls ty) =
  case subst theta ty of
    ty'@(TypeConstrained tys tv) -> case filter (hasInstance inEnv qcls) tys of
      []     -> do report $ errMissingInstance m p what doc (Pred qcls ty')
                   return theta
      [ty''] -> return (bindSubst tv ty'' theta)
      tys' | length tys == length tys' -> return theta
           | otherwise                 -> liftM (flip (bindSubst tv) theta)
                                                (freshConstrained tys')
    ty' | hasInstance inEnv qcls ty' -> return theta
        | otherwise                  -> do
      report $ errMissingInstance m p what doc (Pred qcls ty')
      return theta

hasInstance :: InstEnv' -> QualIdent -> Type -> Bool
hasInstance inEnv qcls = isJust . instPredSet inEnv qcls

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

applyDefaults :: HasPosition p => p -> String -> Doc -> Set.Set Int -> PredSet
              -> Type -> TCM PredSet
applyDefaults p what doc fvs ps ty = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  inEnv <- getInstEnv
  defs <- getDefaultTypes
  let theta = foldr (bindDefault defs inEnv ps) idSubst $ nub
                [tv | Pred qcls (TypeVariable tv) <- Set.toList ps
                    , tv `Set.notMember` fvs, isNumClass clsEnv qcls]
      ps' = fst (partitionPredSet (subst theta ps))
      ty' = subst theta ty
      tvs' = nub $ filter (`Set.notMember` fvs) (typeVars ps')
  mapM_ (report . errAmbiguousTypeVariable m p what doc (TypeContext ps' ty'))
        tvs'
  modifyTypeSubst $ compose theta
  return ps'

bindDefault :: [Type] -> InstEnv' -> PredSet -> Int -> TypeSubst -> TypeSubst
bindDefault defs inEnv ps tv =
  case foldr (defaultType inEnv tv) defs (Set.toList ps) of
    []   -> id
    ty:_ -> bindSubst tv ty

defaultType :: InstEnv' -> Int -> Pred -> [Type] -> [Type]
defaultType inEnv tv (Pred qcls (TypeVariable tv'))
  | tv == tv' = filter (hasInstance inEnv qcls)
  | otherwise = id
defaultType _     _  _ = id

isNumClass :: ClassEnv -> QualIdent -> Bool
isNumClass = (elem qNumId .) . flip allSuperClasses

-- -----------------------------------------------------------------------------
-- Instantiation and Generalization
-- -----------------------------------------------------------------------------

-- We use negative offsets for fresh type variables.

fresh :: (Int -> a) -> TCM a
fresh f = f <$> getNextId

freshVar :: (Int -> a) -> TCM a
freshVar f = fresh $ \n -> f (- n)

freshTypeVar :: TCM Type
freshTypeVar = freshVar TypeVariable

freshPredType :: [QualIdent] -> TCM (PredSet, Type)
freshPredType qclss = do
  ty <- freshTypeVar
  return (foldr (\qcls -> Set.insert $ Pred qcls ty) emptyPredSet qclss, ty)

freshEnumType :: TCM (PredSet, Type)
freshEnumType = freshPredType [qEnumId]

freshNumType :: TCM (PredSet, Type)
freshNumType = freshPredType [qNumId]

freshFractionalType :: TCM (PredSet, Type)
freshFractionalType = freshPredType [qFractionalId]

freshMonadType :: TCM (PredSet, Type)
freshMonadType = freshPredType [qMonadId]

freshConstrained :: [Type] -> TCM Type
freshConstrained = freshVar . TypeConstrained

inst :: Type -> TCM (PredSet, Type)
inst (TypeForall vs (TypeContext ps ty)) = do
  tys <- replicateM (length vs) freshTypeVar
  let sigma = foldr2 bindSubst idSubst vs tys
  return (subst sigma ps, subst sigma ty)
inst (TypeForall vs ty) = inst (TypeForall vs (predType ty))
inst ty                 = return (emptyPredSet, ty)

-- | Generalizes a predicate set and a type into a type scheme by universally
-- quantifying all type variables that are free in the type and not fixed by
-- the environment. The set of the latter is given by the first parameter.
gen :: Set.Set Int -> PredSet -> Type -> Type
gen gvs ps ty = TypeForall tvs (subst theta (TypeContext ps ty))
  where
    tvs = [tv | tv <- nub (typeVars ty), tv `Set.notMember` gvs]
    tvs' = map TypeVariable [0..]
    theta = foldr2 bindSubst idSubst tvs tvs'

skolemise :: Type -> TCM (PredSet, Type)
skolemise (TypeForall tvs (TypeContext ps ty)) = do
  tvs' <- replicateM (length tvs) freshTypeVar
  let sigma = foldr2 bindSubst idSubst tvs tvs'
  let ps' = subst sigma ps
  (ps'', ty'') <- skolemise (subst sigma ty)
  return (Set.union ps' ps'', ty'')
skolemise (TypeForall tvs ty) = do
  tvs' <- replicateM (length tvs) freshTypeVar
  let sigma = foldr2 bindSubst idSubst tvs tvs'
  skolemise (subst sigma ty)
skolemise (TypeArrow ty1 ty2) = do
  (ps, ty2') <- skolemise ty2
  return (ps, TypeArrow ty1 ty2')
skolemise ty                  = return (emptyPredSet, ty)

-- -----------------------------------------------------------------------------
-- Auxiliary functions
-- -----------------------------------------------------------------------------

-- The functions 'constrType', 'varType', 'funType' and 'labelType' are used to
-- retrieve the type of constructors, pattern variables, variables and labels
-- in expressions, respectively, from the value environment. Because the
-- syntactical correctness has already been verified by the syntax checker, none
-- of these functions should fail.

-- Note that 'varType' can handle ambiguous identifiers and returns the first
-- available type. This function is used for looking up the type of an
-- identifier on the left hand side of a rule where it unambiguously refers to
-- the local definition.

-- The function 'constrLabels' returns a list of all labels belonging to a data
-- constructor. The function 'varArity' works like 'varType' but returns a
-- variable's arity instead of its type.

constrType :: ModuleIdent -> QualIdent -> ValueEnv -> Type
constrType m c vEnv = case qualLookupValue c vEnv of
  [DataConstructor _ _ _ tySc]  -> tySc
  [NewtypeConstructor _ _ tySc] -> tySc
  _ -> case qualLookupValue (qualQualify m c) vEnv of
         [DataConstructor _ _ _ tySc]  -> tySc
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

varType :: Ident -> ValueEnv -> Type
varType v vEnv = case lookupValue v vEnv of
  Value _ _ _ tySc : _ -> tySc
  _                    -> internalError $ "TypeCheck.varType: " ++ show v

varArity :: QualIdent -> ValueEnv -> Int
varArity v vEnv = case qualLookupValue v vEnv of
  Value _ _ n _ : _ -> n
  Label _ _ _ : _   -> 1
  _                 -> internalError $ "TypeCheck.varArity: " ++ show v

funType :: ModuleIdent -> QualIdent -> ValueEnv -> Type
funType m f vEnv = case qualLookupValue f vEnv of
  [Value _ _ _ tySc] -> tySc
  [Label _ _ tySc]   -> tySc
  _ -> case qualLookupValue (qualQualify m f) vEnv of
         [Value _ _ _ tySc] -> tySc
         [Label _ _ tySc]   -> tySc
         _                  -> internalError $ "TypeCheck.funType: " ++ show f

labelType :: ModuleIdent -> QualIdent -> ValueEnv -> Type
labelType m l vEnv = case qualLookupValue l vEnv of
  [Label _ _ tySc] -> tySc
  _ -> case qualLookupValue (qualQualify m l) vEnv of
         [Label _ _ tySc] -> tySc
         _                -> internalError $ "TypeCheck.labelType: " ++ show l

-- | Handles the expansion of type aliases in a type expression. The resulting
-- type will start with a predicate set.
expandPoly :: TypeExpr -> TCM Type
expandPoly ty = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  clsEnv <- getClassEnv
  return $ expandPolyType m tcEnv clsEnv ty

-- | Handles the expansion of type aliases in a type expression.
expandMono :: [Ident] -> TypeExpr -> TCM Type
expandMono tvs ty = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  clsEnv <- getClassEnv
  return $ expandMonoType m tcEnv clsEnv tvs ty

-- | Splits a predicate set into a pair of predicate sets such that all type
-- variables that appear in the types of the predicates in the first predicate
-- set are elements of a given set of type variables.
splitPredSet :: Set.Set Int -> PredSet -> (PredSet, PredSet)
splitPredSet fvs = Set.partition (all (`Set.member` fvs) . typeVars)

-- | Computes the set of free type variables of a type environment. We ignore
-- the types of data constructors here because we know that they are closed.
fvEnv :: ValueEnv -> Set.Set Int
fvEnv vEnv = Set.fromList [tv | tySc <- localTypes vEnv,
                                tv <- typeVars (rawPredType tySc), tv < 0]

computeFvEnv :: TCM (Set.Set Int)
computeFvEnv = do
  theta <- getTypeSubst
  vEnv <- getValueEnv
  return $ fvEnv (subst theta vEnv)

localTypes :: ValueEnv -> [Type]
localTypes vEnv = [tySc | (_, Value _ _ _ tySc) <- localBindings vEnv]

-- -----------------------------------------------------------------------------
-- Error functions
-- -----------------------------------------------------------------------------

errPolymorphicVar :: Ident -> Message
errPolymorphicVar v = posMessage v $ hsep $ map text
  ["Variable", idName v, "has a polymorphic type"]

errTypeSigTooGeneral :: HasPosition a => a -> ModuleIdent -> Doc -> TypeExpr
                     -> Type -> Message
errTypeSigTooGeneral p m what qty ty = posMessage p $ vcat
  [ text "Type signature too general", what
  , text "Inferred type:" <+> ppType m ty
  , text "Type signature:" <+> ppTypeExpr 0 qty ]

errMethodTypeTooSpecific :: HasPosition a => a -> ModuleIdent -> Doc -> Type
                         -> Type -> Message
errMethodTypeTooSpecific p m what ety ity = posMessage p $ vcat
  [ text "Method type too specific", what
  , text "Inferred type:" <+> ppType m ity
  , text "Expected type:" <+> ppType m ety ]

errNonFunctionType :: HasPosition a => a -> String -> Doc -> ModuleIdent -> Type
                   -> Message
errNonFunctionType p what doc m ty = posMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be applied" ]

errNonBinaryOp :: HasPosition a => a -> String -> Doc -> ModuleIdent -> Type
               -> Message
errNonBinaryOp p what doc m ty = posMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be used as binary operator" ]

errTypeMismatch :: HasPosition a => a -> String -> Doc -> ModuleIdent -> Type
                -> Type -> Doc -> Message
errTypeMismatch p what doc m ety ity reason = posMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Inferred type:" <+> ppType m ity
  , text "Expected type:" <+> ppType m ety
  , reason ]

errRecursiveType :: ModuleIdent -> Int -> Type -> Doc
errRecursiveType m tv = errIncompatibleTypes m (TypeVariable tv)

errIncompatibleTypes :: ModuleIdent -> Type -> Type -> Doc
errIncompatibleTypes m ty1 ty2 = sep
  [ text "Types" <+> ppType m ty1
  , nest 2 $ text "and" <+> ppType m ty2
  , text "are incompatible" ]

errIncompatibleLabelTypes :: HasPosition a => a -> ModuleIdent -> Ident -> Type
                          -> Type -> Message
errIncompatibleLabelTypes p m l ty1 ty2 = posMessage p $ sep
  [ text "Labeled types" <+> ppIdent l <+> text "::" <+> ppType m ty1
  , nest 10 $ text "and" <+> ppIdent l <+> text "::" <+> ppType m ty2
  , text "are incompatible" ]

errMissingInstance :: HasPosition a => ModuleIdent -> a -> String -> Doc -> Pred
                   -> Message
errMissingInstance m p what doc pr = posMessage p $ vcat
  [ text "Missing instance for" <+> ppPred m pr
  , text "in" <+> text what
  , doc ]

errAmbiguousTypeVariable :: HasPosition a => ModuleIdent -> a -> String -> Doc
                         -> Type -> Int -> Message
errAmbiguousTypeVariable m p what doc ty tv = posMessage p $ vcat
  [ text "Ambiguous type variable" <+> ppType m (TypeVariable tv)
  , text "in type" <+> ppType m ty
  , text "inferred for" <+> text what
  , doc ]
