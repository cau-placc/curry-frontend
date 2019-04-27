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
{-# LANGUAGE CPP #-}
module Checks.TypeCheck (typeCheck) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Monad.Extra        ( (&&^), allM, filterM, foldM
                                            , liftM, notM, replicateM, unless
                                            , unlessM )
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List                  (nub, nubBy, partition, sortBy)
import           Data.Function              (on)
import qualified Data.Map            as Map (Map, empty, insert, lookup)
import           Data.Maybe                 (fromJust, fromMaybe, isJust)
import qualified Data.Set.Extra      as Set ( Set, concatMap, deleteMin, empty
                                            , fromList, insert, member
                                            , notMember, partition, singleton
                                            , toList, union, unions )

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Base.SpanInfo
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.CurryTypes
import Base.Expr
import Base.Kinds
import Base.Messages (Message, posMessage, internalError)
import Base.SCC
import Base.TopEnv
import Base.TypeExpansion
import Base.Types
import Base.TypeSubst
import Base.Utils (foldr2, fst3, snd3, thd3, uncurry3, mapAccumM)

import Env.Class
import Env.Instance
import Env.TypeConstructor
import Env.Value

-- Type checking proceeds as follows. First, the types of all data
-- constructors, field labels and class methods are entered into the
-- value environment and then a type inference for all function and
-- value definitions is performed.

typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> InstEnv -> [Decl a]
          -> ([Decl PredType], ValueEnv, [Message])
typeCheck m tcEnv vEnv clsEnv inEnv ds = runTCM (checkDecls ds) initState
  where initState = TcState m tcEnv vEnv clsEnv (inEnv, Map.empty)
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
-- the dynamic part of the environment.

type TCM = S.State TcState

type InstEnv' = (InstEnv, Map.Map QualIdent [Type])

data TcState = TcState
  { moduleIdent  :: ModuleIdent -- read only
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
               in  (a, typeSubst s' `subst` valueEnv s', reverse $ errors s')

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
bindConstr m n ty (DataConstr c _ ps tys) =
  bindGlobalInfo (\qc tyScheme -> DataConstructor qc arity ls tyScheme) m c
                 (ForAll n (PredType ps (foldr TypeArrow ty tys)))
  where arity = length tys
        ls    = replicate arity anonId
bindConstr m n ty (RecordConstr c _ ps ls tys) =
  bindGlobalInfo (\qc tyScheme -> DataConstructor qc arity ls tyScheme) m c
                 (ForAll n (PredType ps (foldr TypeArrow ty tys)))
  where arity = length tys

bindNewConstr :: ModuleIdent -> Int -> Type -> DataConstr -> ValueEnv
              -> ValueEnv
bindNewConstr m n cty (DataConstr c _ _ [lty]) =
  bindGlobalInfo (\qc tyScheme -> NewtypeConstructor qc anonId tyScheme) m c
                 (ForAll n (predType (TypeArrow lty cty)))
bindNewConstr m n cty (RecordConstr c _ _ [l] [lty]) =
  bindGlobalInfo (\qc tyScheme -> NewtypeConstructor qc l tyScheme) m c
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
  where labels = [(l, p, ty) | RecordDecl _ _ _ _ fs <- cs,
                               FieldDecl p ls ty <- fs, l <- ls]
checkFieldLabel (NewtypeDecl _ _ tvs (NewRecordDecl p _ (l, ty)) _) = do
  _ <- tcFieldLabel tvs (l, p, ty)
  ok
checkFieldLabel _ = ok

tcFieldLabel :: HasPosition p => [Ident] -> (Ident, p, TypeExpr)
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

tcFieldLabels :: HasPosition p => (Ident, p, [Type]) -> TCM ()
tcFieldLabels (_, _, [])     = return ()
tcFieldLabels (l, p, ty:tys) = unless (not (any (ty /=) tys)) $ do
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
        constr l = map (qualifyLike tc) $
          [constrIdent c | c <- cs, l `elem` recLabels c]
        sameLabel (l1,_,_) (l2,_,_) = l1 == l2
    bindData (RenamingType tc k (RecordConstr c _ _ [l] [lty])) vEnv' =
      bindLabel m n (constrType' tc n) (l, [qc], lty) vEnv'
      where
        n = kindArity k
        qc = qualifyLike tc c
    bindData (RenamingType _ _ (RecordConstr _ _ _ _ _)) _ =
      internalError $ "Checks.TypeCheck.bindLabels'.bindData: " ++
        "RenamingType with more than one record label"
    bindData _ vEnv' = vEnv'

bindLabel :: ModuleIdent -> Int -> Type -> (Ident, [QualIdent], Type)
          -> ValueEnv -> ValueEnv
bindLabel m n ty (l, lcs, lty) =
  bindGlobalInfo (\qc tyScheme -> Label qc lcs tyScheme) m l
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
    bindMethods (TypeClass _ _ ms) vEnv' =
      foldr (bindClassMethod m) vEnv' ms
    bindMethods _ vEnv' = vEnv'

-- Since the implementations of class methods can differ in their arity,
-- we assume an arity of 0 when we enter one into the value environment.

bindClassMethod :: ModuleIdent -> ClassMethod -> ValueEnv -> ValueEnv
bindClassMethod m (ClassMethod f _ pty) =
  bindGlobalInfo (\qc tySc -> Value qc True 0 tySc) m f (typeScheme pty)

-- Default Types:
-- The list of default types is given either by a default declaration in
-- the source code or defaults to the predefined list of numeric data types.

setDefaults :: Decl a -> TCM ()
setDefaults (DefaultDecl _ tys) = mapM toDefaultType tys >>= setDefaultTypes
  where
    toDefaultType =
      liftM snd . (inst =<<) . liftM typeScheme
                . expandPoly . QualTypeExpr NoSpanInfo []
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
bindTypeSigs (TypeSig _ vs qty) env =
  foldr (flip bindTypeSig qty) env vs
bindTypeSigs _                  env = env

lookupTypeSig :: Ident -> SigEnv -> Maybe QualTypeExpr
lookupTypeSig = Map.lookup

-- Declaration groups:
-- Before type checking a group of declarations, a dependency analysis is
-- performed and the declaration group is eventually transformed into
-- nested declaration groups which are checked separately. Within each
-- declaration group, first the value environment is extended with new
-- bindings for all variables and functions defined in the group. Next,
-- types are inferred for all declarations without an explicit type signature
-- and the inferred types are then generalized. Finally, the types of all
-- explicitly typed declarations are checked.

-- Within a group of mutually recursive declarations, all type variables
-- that appear in the types of the variables defined in the group and
-- whose type cannot be generalized must not be generalized in the other
-- declarations of that group as well.

tcDecls :: [Decl a] -> TCM (PredSet, [Decl PredType])
tcDecls = liftM (fmap fromPDecls) . tcPDecls . toPDecls

tcPDecls :: [PDecl a] -> TCM (PredSet, [PDecl PredType])
tcPDecls pds = withLocalSigEnv $ do
  let (vpds, opds) = partition (isValueDecl . snd) pds
  setSigEnv $ foldr (bindTypeSigs . snd) emptySigEnv $ opds
  m <- getModuleIdent
  (ps, vpdss') <-
    mapAccumM tcPDeclGroup emptyPredSet $ scc (bv . snd) (qfv m . snd) vpds
  return (ps, map untyped opds ++ concat (vpdss' :: [[PDecl PredType]]))

tcPDeclGroup :: PredSet -> [PDecl a] -> TCM (PredSet, [PDecl PredType])
tcPDeclGroup ps [(i, ExternalDecl p fs)] = do
  tys <- mapM (tcExternal . varIdent) fs
  return (ps, [(i, ExternalDecl p (zipWith (fmap . const . predType) tys fs))])
tcPDeclGroup ps [(i, FreeDecl p fvs)] = do
  vs <- mapM (tcDeclVar False) (bv fvs)
  m <- getModuleIdent
  modifyValueEnv $ flip (bindVars m) vs
  return (ps, [(i, FreeDecl p (map (\(v, _, ForAll _ pty) -> Var pty v) vs))])
tcPDeclGroup ps pds = do
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

partitionPDecls :: SigEnv -> [PDecl a] -> ([PDecl a], [(QualTypeExpr, PDecl a)])
partitionPDecls sigs =
  foldr (\pd -> maybe (implicit pd) (explicit pd) (typeSig $ snd pd)) ([], [])
  where implicit pd ~(impPds, expPds) = (pd : impPds, expPds)
        explicit pd qty ~(impPds, expPds) = (impPds, (qty, pd) : expPds)
        typeSig (FunctionDecl _ _ f _) = lookupTypeSig f sigs
        typeSig (PatternDecl _ (VariablePattern _ _ v) _) = lookupTypeSig v sigs
        typeSig _ = Nothing

bindVars :: ModuleIdent -> ValueEnv -> [(Ident, Int, TypeScheme)] -> ValueEnv
bindVars m = foldr $ uncurry3 $ flip (bindFun m) False

rebindVars :: ModuleIdent -> ValueEnv -> [(Ident, Int, TypeScheme)] -> ValueEnv
rebindVars m = foldr $ uncurry3 $ flip (rebindFun m) False

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
      | poly || null (fv qty) -> do
        pty <- expandPoly qty
        return (v, 0, typeScheme pty)
      | otherwise -> do
        report $ errPolymorphicVar v
        lambdaVar v
    Nothing -> lambdaVar v

tcPDecl :: PredSet -> PDecl a -> TCM (PredSet, (Type, PDecl PredType))
tcPDecl ps (i, FunctionDecl p _ f eqs) = do
  vEnv <- getValueEnv
  tcFunctionPDecl i ps (varType f vEnv) p f eqs
tcPDecl ps (i, d@(PatternDecl p t rhs)) = do
  (ps', ty', t') <- tcPattern p t
  (ps'', rhs') <- tcRhs rhs >>-
    unifyDecl p "pattern declaration" (ppDecl d) (ps `Set.union` ps') ty'
  return (ps'', (ty', (i, PatternDecl p t' rhs')))
tcPDecl _ _ = internalError "TypeCheck.tcPDecl"

-- The function 'tcFunctionPDecl' ignores the context of a function's type
-- signature. This prevents missing instance errors when the inferred type
-- of a function is less general than the declared type.

tcFunctionPDecl :: Int -> PredSet -> TypeScheme -> SpanInfo -> Ident
                -> [Equation a] -> TCM (PredSet, (Type, PDecl PredType))
tcFunctionPDecl i ps tySc@(ForAll _ pty) p f eqs = do
  (_, ty) <- inst tySc
  fs <- computeFsEnv
  (ps', eqs') <- mapAccumM (tcEquation fs ty) ps eqs
  return (ps', (ty, (i, FunctionDecl p pty f eqs')))

tcEquation :: Set.Set Int -> Type -> PredSet -> Equation a
           -> TCM (PredSet, Equation PredType)
tcEquation fs ty ps eqn@(Equation p lhs rhs) =
  tcEqn fs p lhs rhs >>- unifyDecl p "equation" (ppEquation eqn) ps ty

tcEqn :: Set.Set Int -> SpanInfo -> Lhs a -> Rhs a
      -> TCM (PredSet, Type, Equation PredType)
tcEqn fs p lhs rhs = do
  (ps, tys, lhs', ps', ty, rhs') <- withLocalValueEnv $ do
    bindLambdaVars lhs
    (ps, tys, lhs') <- tcLhs p lhs
    (ps', ty, rhs') <- tcRhs rhs
    return (ps, tys, lhs', ps', ty, rhs')
  ps'' <- reducePredSet p "equation" (ppEquation (Equation p lhs' rhs'))
                        (ps `Set.union` ps')
  checkSkolems p "Equation" ppEquation fs ps'' (foldr TypeArrow ty tys)
    (Equation p lhs' rhs')

bindLambdaVars :: QuantExpr t => t -> TCM ()
bindLambdaVars t = do
  m <- getModuleIdent
  vs <- mapM lambdaVar (nub $ bv t)
  modifyValueEnv $ flip (bindVars m) vs

lambdaVar :: Ident -> TCM (Ident, Int, TypeScheme)
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

fixType :: TypeScheme -> PDecl PredType -> PDecl PredType
fixType ~(ForAll _ pty) (i, FunctionDecl p _ f eqs) =
  (i, FunctionDecl p pty f eqs)
fixType ~(ForAll _ pty) pd@(i, PatternDecl p t rhs) = case t of
  VariablePattern spi _ v
    -> (i, PatternDecl p (VariablePattern spi pty v) rhs)
  _ -> pd
fixType _ _ = internalError "TypeCheck.fixType"

declVars :: Decl PredType -> [(Ident, Int, TypeScheme)]
declVars (FunctionDecl _ pty f eqs) = [(f, eqnArity $ head eqs, typeScheme pty)]
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

tcCheckPDecl :: PredSet -> QualTypeExpr -> PDecl a
             -> TCM (PredSet, PDecl PredType)
tcCheckPDecl ps qty pd = do
  (ps', (ty, pd')) <- tcPDecl ps pd
  fvs <- computeFvEnv
  theta <- getTypeSubst
  poly <- isNonExpansive $ snd pd
  let (gps, lps) = splitPredSet fvs ps'
      ty' = subst theta ty
      tySc = if poly then gen fvs lps ty' else monoType ty'
  checkPDeclType qty gps tySc pd'

checkPDeclType :: QualTypeExpr -> PredSet -> TypeScheme -> PDecl PredType
               -> TCM (PredSet, PDecl PredType)
checkPDeclType qty ps tySc (i, FunctionDecl p _ f eqs) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral p m (text "Function:" <+> ppIdent f) qty tySc
  return (ps, (i, FunctionDecl p pty f eqs))
checkPDeclType qty ps tySc (i, PatternDecl p (VariablePattern spi _ v) rhs) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral p m (text "Variable:" <+> ppIdent v) qty tySc
  return (ps, (i, PatternDecl p (VariablePattern spi pty v) rhs))
checkPDeclType _ _ _ _ = internalError "TypeCheck.checkPDeclType"

checkTypeSig :: PredType -> TypeScheme -> TCM Bool
checkTypeSig (PredType sigPs sigTy) (ForAll _ (PredType ps ty)) = do
  clsEnv <- getClassEnv
  return $
    ty `eqTypes` sigTy &&
    all (`Set.member` maxPredSet clsEnv sigPs) (Set.toList ps)

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
 eq is (TypeSkolem          i1) (TypeSkolem          i2) = eqVar is i1 i2
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

tcTopPDecl :: PDecl a -> TCM (PDecl PredType)
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
  pty <- expandPoly $ QualTypeExpr NoSpanInfo cx ty
  mid <- getModuleIdent
  let origCls = getOrigName mid qcls tcEnv
      clsQual = head $ filter isQualified $ reverseLookupByOrigName origCls tcEnv
      qQualCls = qualQualify (fromJust $ qidModule clsQual) qcls
  vpds' <- mapM (tcInstanceMethodPDecl qQualCls pty) vpds
  return (i, InstanceDecl p cx qcls ty $ fromPDecls $ map untyped opds ++ vpds')
  where (vpds, opds) = partition (isValueDecl . snd) $ toPDecls ds
tcTopPDecl _ = internalError "Checks.TypeCheck.tcTopDecl"

tcClassMethodPDecl :: QualIdent -> Ident -> PDecl a -> TCM (PDecl PredType)
tcClassMethodPDecl qcls tv pd@(_, FunctionDecl _ _ f _) = do
  methTy <- classMethodType qualify f
  (tySc, pd') <- tcMethodPDecl methTy pd
  sigs <- getSigEnv
  let QualTypeExpr spi cx ty = fromJust $ lookupTypeSig f sigs
      qty = QualTypeExpr spi
              (Constraint NoSpanInfo qcls (VariableType NoSpanInfo tv) : cx) ty
  checkClassMethodType qty tySc pd'
tcClassMethodPDecl _ _ _ = internalError "TypeCheck.tcClassMethodPDecl"

tcInstanceMethodPDecl :: QualIdent -> PredType -> PDecl a
                      -> TCM (PDecl PredType)
tcInstanceMethodPDecl qcls pty pd@(_, FunctionDecl _ _ f _) = do
  methTy <- instMethodType (qualifyLike qcls) pty f
  (tySc, pd') <- tcMethodPDecl (typeScheme methTy) pd
  checkInstMethodType (normalize 0 methTy) tySc pd'
tcInstanceMethodPDecl _ _ _ = internalError "TypeCheck.tcInstanceMethodPDecl"

tcMethodPDecl :: TypeScheme -> PDecl a -> TCM (TypeScheme, PDecl PredType)
tcMethodPDecl tySc (i, FunctionDecl p _ f eqs) = withLocalValueEnv $ do
  m <- getModuleIdent
  modifyValueEnv $ bindFun m f True (eqnArity $ head eqs) tySc
  (ps, (ty, pd)) <- tcFunctionPDecl i emptyPredSet tySc p f eqs
  theta <- getTypeSubst
  return (gen Set.empty ps $ subst theta ty, pd)
tcMethodPDecl _ _ = internalError "TypeCheck.tcMethodPDecl"

checkClassMethodType :: QualTypeExpr -> TypeScheme -> PDecl PredType
                     -> TCM (PDecl PredType)
checkClassMethodType qty tySc pd@(_, FunctionDecl p _ f _) = do
  pty <- expandPoly qty
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $ errTypeSigTooGeneral p m (text "Method:" <+> ppIdent f) qty tySc
  return pd
checkClassMethodType _ _ _ = internalError "TypeCheck.checkClassMethodType"

checkInstMethodType :: PredType -> TypeScheme -> PDecl PredType
                    -> TCM (PDecl PredType)
checkInstMethodType pty tySc pd@(_, FunctionDecl p _ f _) = do
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $
      errMethodTypeTooSpecific p m (text "Method:" <+> ppIdent f) pty tySc
  return pd
checkInstMethodType _ _ _ = internalError "TypeCheck.checkInstMethodType"

classMethodType :: (Ident -> QualIdent) -> Ident -> TCM TypeScheme
classMethodType qual f = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  return $ funType m (qual $ unRenameIdent f) vEnv

-- Due to the sorting of the predicate set, we can simply remove the minimum
-- element as this is guaranteed to be the class constraint (see module 'Types'
-- for more information).

instMethodType :: (Ident -> QualIdent) -> PredType -> Ident -> TCM PredType
instMethodType qual (PredType ps ty) f = do
  ForAll _ (PredType ps' ty') <- classMethodType qual f
  let PredType ps'' ty'' = instanceType ty (PredType (Set.deleteMin ps') ty')
  return $ PredType (ps `Set.union` ps'') ty''

-- External functions:

tcExternal :: Ident -> TCM Type
tcExternal f = do
  sigs <- getSigEnv
  case lookupTypeSig f sigs of
    Nothing -> internalError "TypeCheck.tcExternal: type signature not found"
    Just (QualTypeExpr _ _ ty) -> do
      m <- getModuleIdent
      PredType _ ty' <- expandPoly $ QualTypeExpr NoSpanInfo [] ty
      modifyValueEnv $ bindFun m f False (arrowArity ty') (polyType ty')
      return ty'

-- Patterns and Expressions:
-- Note that the type attribute associated with a constructor or infix
-- pattern is the type of the whole pattern and not the type of the
-- constructor itself. Overloaded (numeric) literals are not supported in
-- patterns.

tcLiteral :: Bool -> Literal -> TCM (PredSet, Type)
tcLiteral _ (Char _) = return (emptyPredSet, charType)
tcLiteral poly (Int _)
  | poly = freshNumType
  | otherwise = liftM ((,) emptyPredSet) (freshConstrained numTypes)
tcLiteral poly (Float _)
  | poly = freshFractionalType
  | otherwise = liftM ((,) emptyPredSet) (freshConstrained fractionalTypes)
tcLiteral _ (String _) = return (emptyPredSet, stringType)

tcLhs :: HasPosition p => p -> Lhs a -> TCM (PredSet, [Type], Lhs PredType)
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
          -> TCM (PredSet, Type, Pattern PredType)
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
  (ps, (tys, ty')) <- liftM (fmap arrowUnapply) (skol (constrType m c vEnv))
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
  (ps, ty) <- liftM (fmap arrowBase) (skol (constrType m c vEnv))
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
              -> ([Pattern PredType] -> [Pattern PredType])
              -> PredSet -> Type -> [Pattern a]
              -> TCM (PredSet, Type, Pattern PredType)
tcFuncPattern _ spi _ f ts ps ty [] =
  return (ps, ty, FunctionPattern spi (predType ty) f (ts []))
tcFuncPattern p spi doc f ts ps ty (t':ts') = do
  (alpha, beta) <-
    tcArrow p "functional pattern" (doc $-$ text "Term:" <+> ppPattern 0 t) ty
  (ps', t'') <- tcPatternArg p "functional pattern" doc ps alpha t'
  tcFuncPattern p spi doc f (ts . (t'' :)) ps' beta ts'
  where t = FunctionPattern spi (predType ty) f (ts [])

tcPatternArg :: HasPosition p => p -> String -> Doc -> PredSet -> Type
             -> Pattern a -> TCM (PredSet, Pattern PredType)
tcPatternArg p what doc ps ty t =
  tcPattern p t >>-
    unify p what (doc $-$ text "Term:" <+> ppPattern 0 t) ps ty

tcRhs :: Rhs a -> TCM (PredSet, Type, Rhs PredType)
tcRhs (SimpleRhs p e ds) = do
  (ps, ds', ps', ty, e') <- withLocalValueEnv $ do
    (ps, ds') <- tcDecls ds
    (ps', ty, e') <- tcExpr p e
    return (ps, ds', ps', ty, e')
  ps'' <- reducePredSet p "expression" (ppExpr 0 e') (ps `Set.union` ps')
  return (ps'', ty, SimpleRhs p e' ds')
tcRhs (GuardedRhs spi es ds) = withLocalValueEnv $ do
  (ps, ds') <- tcDecls ds
  ty <- freshTypeVar
  (ps', es') <- mapAccumM (tcCondExpr ty) ps es
  return (ps', ty, GuardedRhs spi es' ds')

tcCondExpr :: Type -> PredSet -> CondExpr a -> TCM (PredSet, CondExpr PredType)
tcCondExpr ty ps (CondExpr p g e) = do
  (ps', g') <- tcExpr p g >>- unify p "guard" (ppExpr 0 g) ps boolType
  (ps'', e') <- tcExpr p e >>- unify p "guarded expression" (ppExpr 0 e) ps' ty
  return (ps'', CondExpr p g' e')

tcExpr :: HasPosition p => p -> Expression a
       -> TCM (PredSet, Type, Expression PredType)
tcExpr _ (Literal spi _ l) = do
  (ps, ty) <- tcLiteral True l
  return (ps, ty, Literal spi (predType ty) l)
tcExpr _ (Variable spi _ v) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- if isAnonId (unqualify v) then freshPredType []
                                        else inst (funType m v vEnv)
  return (ps, ty, Variable spi (predType ty) v)
tcExpr _ (Constructor spi _ c) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- inst (constrType m c vEnv)
  return (ps, ty, Constructor spi (predType ty) c)
tcExpr p (Paren spi e) = do
  (ps, ty, e') <- tcExpr p e
  return (ps, ty, Paren spi e')
tcExpr p (Typed spi e qty) = do
  pty <- expandPoly qty
  (ps, ty) <- inst (typeScheme pty)
  (ps', e') <- tcExpr p e >>-
    unifyDecl p "explicitly typed expression" (ppExpr 0 e) emptyPredSet ty
  fvs <- computeFvEnv
  theta <- getTypeSubst
  let (gps, lps) = splitPredSet fvs ps'
      tySc = gen fvs lps (subst theta ty)
  unlessM (checkTypeSig pty tySc) $ do
    m <- getModuleIdent
    report $
      errTypeSigTooGeneral p m (text "Expression:" <+> ppExpr 0 e) qty tySc
  return (ps `Set.union` gps, ty, Typed spi e' qty)
tcExpr _ e@(Record spi _ c fs) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps, ty) <- liftM (fmap arrowBase) (inst (constrType m c vEnv))
  (ps', fs') <- mapAccumM (tcField tcExpr "construction"
    (\e' -> ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e') ty) ps fs
  return (ps', ty, Record spi (predType ty) c fs')
tcExpr p e@(RecordUpdate spi e1 fs) = do
  (ps, ty, e1') <- tcExpr p e1
  (ps', fs') <- mapAccumM (tcField tcExpr "update"
    (\e' -> ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e') ty) ps fs
  return (ps', ty, RecordUpdate spi e1' fs')
tcExpr p (Tuple spi es) = do
  (pss, tys, es') <- liftM unzip3 $ mapM (tcExpr p) es
  return (Set.unions pss, tupleType tys, Tuple spi es')
tcExpr p e@(List spi _ es) = do
  ty <- freshTypeVar
  (ps, es') <-
    mapAccumM (flip (tcArg p "expression" (ppExpr 0 e)) ty) emptyPredSet es
  return (ps, listType ty, List spi (predType $ listType ty) es')
tcExpr p (ListCompr spi e qs) = do
  fs <- computeFsEnv
  (ps, qs', ps', ty, e') <- withLocalValueEnv $ do
    (ps, qs') <- mapAccumM (tcQual p) emptyPredSet qs
    (ps', ty, e') <- tcExpr p e
    return (ps, qs', ps', ty, e')
  ps'' <- reducePredSet p "expression" (ppExpr 0 e') (ps `Set.union` ps')
  checkSkolems p "Expression" (ppExpr 0) fs ps'' (listType ty)
    (ListCompr spi e' qs')
tcExpr p e@(EnumFrom spi e1) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  return (ps', listType ty, EnumFrom spi e1')
tcExpr p e@(EnumFromThen spi e1 e2) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  (ps'', e2') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps' ty e2
  return (ps'', listType ty, EnumFromThen spi e1' e2')
tcExpr p e@(EnumFromTo spi e1 e2) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  (ps'', e2') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps' ty e2
  return (ps'', listType ty, EnumFromTo spi e1' e2')
tcExpr p e@(EnumFromThenTo spi e1 e2 e3) = do
  (ps, ty) <- freshEnumType
  (ps', e1') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps ty e1
  (ps'', e2') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps' ty e2
  (ps''', e3') <- tcArg p "arithmetic sequence" (ppExpr 0 e) ps'' ty e3
  return (ps''', listType ty, EnumFromThenTo spi e1' e2' e3')
tcExpr p e@(UnaryMinus spi e1) = do
  (ps, ty) <- freshNumType
  (ps', e1') <- tcArg p "unary negation" (ppExpr 0 e) ps ty e1
  return (ps', ty, UnaryMinus spi e1')
tcExpr p e@(Apply spi e1 e2) = do
  (ps, (alpha, beta), e1') <- tcExpr p e1 >>=-
    tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
  (ps', e2') <- tcArg p "application" (ppExpr 0 e) ps alpha e2
  return (ps', beta, Apply spi e1' e2')
tcExpr p e@(InfixApply spi e1 op e2) = do
  (ps, (alpha, beta, gamma), op') <- tcInfixOp op >>=-
    tcBinary p "infix application" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
  (ps', e1') <- tcArg p "infix application" (ppExpr 0 e) ps alpha e1
  (ps'', e2') <- tcArg p "infix application" (ppExpr 0 e) ps' beta e2
  return (ps'', gamma, InfixApply spi e1' op' e2')
tcExpr p e@(LeftSection spi e1 op) = do
  (ps, (alpha, beta), op') <- tcInfixOp op >>=-
    tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
  (ps', e1') <- tcArg p "left section" (ppExpr 0 e) ps alpha e1
  return (ps', beta, LeftSection spi e1' op')
tcExpr p e@(RightSection spi op e1) = do
  (ps, (alpha, beta, gamma), op') <- tcInfixOp op >>=-
    tcBinary p "right section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
  (ps', e1') <- tcArg p "right section" (ppExpr 0 e) ps beta e1
  return (ps', TypeArrow alpha gamma, RightSection spi op' e1')
tcExpr p (Lambda spi ts e) = do
  fs <- computeFsEnv
  (pss, tys, ts', ps, ty, e')<- withLocalValueEnv $ do
    bindLambdaVars ts
    (pss, tys, ts') <- liftM unzip3 $ mapM (tcPattern p) ts
    (ps, ty, e') <- tcExpr p e
    return (pss, tys, ts', ps, ty, e')
  ps' <- reducePredSet p "expression" (ppExpr 0 e') (Set.unions $ ps : pss)
  checkSkolems p "Expression" (ppExpr 0) fs ps' (foldr TypeArrow ty tys)
    (Lambda spi ts' e')
tcExpr p (Let spi ds e) = do
  fs <- computeFsEnv
  (ps, ds', ps', ty, e') <- withLocalValueEnv $ do
    (ps, ds') <- tcDecls ds
    (ps', ty, e') <- tcExpr p e
    return (ps, ds', ps', ty, e')
  ps'' <- reducePredSet p "expression" (ppExpr 0 e') (ps `Set.union` ps')
  checkSkolems p "Expression" (ppExpr 0) fs ps'' ty (Let spi ds' e')
tcExpr p (Do spi sts e) = do
  fs <- computeFsEnv
  (sts', ty, ps', e') <- withLocalValueEnv $ do
    ((ps, mTy), sts') <-
      mapAccumM (uncurry (tcStmt p)) (emptyPredSet, Nothing) sts
    ty <- liftM (maybe id TypeApply mTy) freshTypeVar
    (ps', e') <- tcExpr p e >>- unify p "statement" (ppExpr 0 e) ps ty
    return (sts', ty, ps', e')
  checkSkolems p "Expression" (ppExpr 0) fs ps' ty (Do spi sts' e')
tcExpr p e@(IfThenElse spi e1 e2 e3) = do
  (ps, e1') <- tcArg p "expression" (ppExpr 0 e) emptyPredSet boolType e1
  (ps', ty, e2') <- tcExpr p e2
  (ps'', e3') <- tcArg p "expression" (ppExpr 0 e) (ps `Set.union` ps') ty e3
  return (ps'', ty, IfThenElse spi e1' e2' e3')
tcExpr p (Case spi ct e as) = do
  (ps, tyLhs, e') <- tcExpr p e
  tyRhs <- freshTypeVar
  fs <- computeFsEnv
  (ps', as') <- mapAccumM (tcAlt fs tyLhs tyRhs) ps as
  return (ps', tyRhs, Case spi ct e' as')

tcArg :: HasPosition p => p -> String -> Doc -> PredSet -> Type -> Expression a
      -> TCM (PredSet, Expression PredType)
tcArg p what doc ps ty e =
  tcExpr p e >>- unify p what (doc $-$ text "Term:" <+> ppExpr 0 e) ps ty

tcAlt :: Set.Set Int -> Type -> Type -> PredSet -> Alt a
      -> TCM (PredSet, Alt PredType)
tcAlt fs tyLhs tyRhs ps a@(Alt p t rhs) =
  tcAltern fs tyLhs p t rhs >>-
    unify p "case alternative" (ppAlt a) ps tyRhs

tcAltern :: Set.Set Int -> Type -> SpanInfo -> Pattern a
         -> Rhs a -> TCM (PredSet, Type, Alt PredType)
tcAltern fs tyLhs p t rhs = do
  (ps, t', ps', ty', rhs') <- withLocalValueEnv $ do
    bindLambdaVars t
    (ps, t') <-
      tcPatternArg p "case pattern" (ppAlt (Alt p t rhs)) emptyPredSet tyLhs t
    (ps', ty', rhs') <- tcRhs rhs
    return (ps, t', ps', ty', rhs')
  ps'' <- reducePredSet p "alternative" (ppAlt (Alt p t' rhs'))
                        (ps `Set.union` ps')
  checkSkolems p "Alternative" ppAlt fs ps'' ty' (Alt p t' rhs')

tcQual :: HasPosition p => p -> PredSet -> Statement a
       -> TCM (PredSet, Statement PredType)
tcQual p ps (StmtExpr spi e) = do
  (ps', e') <- tcExpr p e >>- unify p "guard" (ppExpr 0 e) ps boolType
  return (ps', StmtExpr spi e')
tcQual _ ps (StmtDecl spi ds) = do
  (ps', ds') <- tcDecls ds
  return (ps `Set.union` ps', StmtDecl spi ds')
tcQual p ps q@(StmtBind spi t e) = do
  alpha <- freshTypeVar
  (ps', e') <- tcArg p "generator" (ppStmt q) ps (listType alpha) e
  bindLambdaVars t
  (ps'', t') <- tcPatternArg p "generator" (ppStmt q) ps' alpha t
  return (ps'', StmtBind spi t' e')

tcStmt :: HasPosition p => p -> PredSet -> Maybe Type -> Statement a
       -> TCM ((PredSet, Maybe Type), Statement PredType)
tcStmt p ps mTy (StmtExpr spi e) = do
  (ps', ty) <- maybe freshMonadType (return . (,) emptyPredSet) mTy
  alpha <- freshTypeVar
  (ps'', e') <- tcExpr p e >>-
    unify p "statement" (ppExpr 0 e) (ps `Set.union` ps') (applyType ty [alpha])
  return ((ps'', Just ty), StmtExpr spi e')
tcStmt _ ps mTy (StmtDecl spi ds) = do
  (ps', ds') <- tcDecls ds
  return ((ps `Set.union` ps', mTy), StmtDecl spi ds')
tcStmt p ps mTy st@(StmtBind spi t e) = do
  (ps', ty) <- maybe freshMonadType (return . (,) emptyPredSet) mTy
  alpha <- freshTypeVar
  (ps'', e') <-
    tcArg p "statement" (ppStmt st) (ps `Set.union` ps') (applyType ty [alpha]) e
  bindLambdaVars t
  (ps''', t') <- tcPatternArg p "statement" (ppStmt st) ps'' alpha t
  return ((ps''', Just ty), StmtBind spi t' e')

tcInfixOp :: InfixOp a -> TCM (PredSet, Type, InfixOp PredType)
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

tcField :: (Position -> a b -> TCM (PredSet, Type, a PredType))
        -> String -> (a b -> Doc) -> Type -> PredSet -> Field (a b)
        -> TCM (PredSet, Field (a PredType))
tcField check what doc ty ps (Field p l x) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  (ps', ty') <- inst (labelType m l vEnv)
  let TypeArrow ty1 ty2 = ty'
  _ <- unify p "field label" empty emptyPredSet ty emptyPredSet ty1
  (ps'', x') <- check (spanInfo2Pos p) x >>-
    unify p ("record " ++ what) (doc x) (ps `Set.union` ps') ty2
  return (ps'', Field p l x')

-- The function 'tcArrow' checks that its argument can be used as
-- an arrow type a -> b and returns the pair (a,b).

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

-- The function 'tcBinary' checks that its argument can be used as an arrow type
-- a -> b -> c and returns the triple (a,b,c).

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

-- Unification: The unification uses Robinson's algorithm.

unify :: HasPosition p => p -> String -> Doc -> PredSet -> Type -> PredSet
      -> Type -> TCM PredSet
unify p what doc ps1 ty1 ps2 ty2 = do
  theta <- getTypeSubst
  let ty1' = subst theta ty1
      ty2' = subst theta ty2
  m <- getModuleIdent
  case unifyTypes m ty1' ty2' of
    Left reason -> report $ errTypeMismatch p what doc m ty1' ty2' reason
    Right sigma -> modifyTypeSubst (compose sigma)
  reducePredSet p what doc $ ps1 `Set.union` ps2

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
unifyTypes _ (TypeSkolem k1) (TypeSkolem k2)
  | k1 == k2 = Right idSubst
unifyTypes m ty1 ty2 = Left (errIncompatibleTypes m ty1 ty2)

unifyTypeLists :: ModuleIdent -> [Type] -> [Type] -> Either Doc TypeSubst
unifyTypeLists _ []           _            = Right idSubst
unifyTypeLists _ _            []           = Right idSubst
unifyTypeLists m (ty1 : tys1) (ty2 : tys2) =
  either Left unifyTypesTheta (unifyTypeLists m tys1 tys2)
  where
    unifyTypesTheta theta =
      either Left (Right . flip compose theta)
                  (unifyTypes m (subst theta ty1) (subst theta ty2))

-- After performing a unification, the resulting substitution is applied
-- to the current predicate set and the resulting predicate set is subject
-- to a reduction. This predicate set reduction retains all predicates whose
-- types are simple variables and which are not implied but other
-- predicates in the predicate set. For all other predicates, the compiler
-- checks whether an instance exists and replaces them by applying the
-- instances' predicate set to the respective types. A minor complication
-- arises due to constrained types, which at present are used to
-- implement overloading of guard expressions and of numeric literals in
-- patterns. The set of admissible types of a constrained type may be
-- restricted by the current predicate set after the reduction and thus
-- may cause a further extension of the current type substitution.

reducePredSet :: HasPosition p => p -> String -> Doc -> PredSet -> TCM PredSet
reducePredSet p what doc ps = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  theta <- getTypeSubst
  inEnv <- (fmap $ fmap $ subst theta) <$> getInstEnv
  let ps' = subst theta ps
      (ps1, ps2) = partitionPredSet $ minPredSet clsEnv $ reducePreds inEnv ps'
  theta' <-
    foldM (reportMissingInstance m p what doc inEnv) idSubst $ Set.toList ps2
  modifyTypeSubst $ compose theta'
  return ps1
  where
    reducePreds inEnv = Set.concatMap $ reducePred inEnv
    reducePred inEnv pr@(Pred qcls ty) =
      maybe (Set.singleton pr) (reducePreds inEnv) (instPredSet inEnv qcls ty)

instPredSet :: InstEnv' -> QualIdent -> Type -> Maybe PredSet
instPredSet inEnv qcls ty = case Map.lookup qcls $ snd inEnv of
  Just tys | ty `elem` tys -> Just emptyPredSet
  _ -> case unapplyType False ty of
    (TypeConstructor tc, tys) ->
      fmap (expandAliasType tys . snd3) (lookupInstInfo (qcls, tc) $ fst inEnv)
    _ -> Nothing

reportMissingInstance :: HasPosition p => ModuleIdent -> p -> String -> Doc
                      -> InstEnv' -> TypeSubst -> Pred -> TCM TypeSubst
reportMissingInstance m p what doc inEnv theta (Pred qcls ty) =
  case subst theta ty of
    ty'@(TypeConstrained tys tv) ->
      case filter (hasInstance inEnv qcls) tys of
        [] -> do
          report $ errMissingInstance m p what doc (Pred qcls ty')
          return theta
        [ty''] -> return (bindSubst tv ty'' theta)
        tys'
          | length tys == length tys' -> return theta
          | otherwise ->
              liftM (flip (bindSubst tv) theta) (freshConstrained tys')
    ty'
      | hasInstance inEnv qcls ty' -> return theta
      | otherwise -> do
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
                [ tv | Pred qcls (TypeVariable tv) <- Set.toList ps
                     , tv `Set.notMember` fvs, isNumClass clsEnv qcls ]
      ps'   = fst (partitionPredSet (subst theta ps))
      ty'   = subst theta ty
      tvs'  = nub $ filter (`Set.notMember` fvs) (typeVars ps')
  mapM_ (report . errAmbiguousTypeVariable m p what doc ps' ty') tvs'
  modifyTypeSubst $ compose theta
  return ps'

bindDefault :: [Type] -> InstEnv' -> PredSet -> Int -> TypeSubst -> TypeSubst
bindDefault defs inEnv ps tv =
  case foldr (defaultType inEnv tv) defs (Set.toList ps) of
    [] -> id
    ty:_ -> bindSubst tv ty

defaultType :: InstEnv' -> Int -> Pred -> [Type] -> [Type]
defaultType inEnv tv (Pred qcls (TypeVariable tv'))
  | tv == tv' = filter (hasInstance inEnv qcls)
  | otherwise = id
defaultType _ _ _ = id

isNumClass :: ClassEnv -> QualIdent -> Bool
isNumClass = (elem qNumId .) . flip allSuperClasses

-- Whenever type inference succeeds for a function equation, case alternative,
-- etc., which may open an existentially quantified data type and thus bring
-- fresh skolem constants into scope, the compiler checks that none of those
-- skolem constants escape their scope through the result type or the type
-- environment. E.g., for the program
--
-- data Key a = forall b . Key b (b -> a)
-- f (Key x _) = x
-- g k x = fcase k of { Key _ f -> f x }
--
-- a skolem constant escapes in the (result) type of 'f' and in the type of the
-- environment variable 'x' for the fcase expression in the definition of 'g'.

checkSkolems :: HasPosition p => p -> String -> (a -> Doc) -> Set.Set Int
             -> PredSet -> Type -> a -> TCM (PredSet, Type, a)
checkSkolems p what pp fs ps ty x = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  theta <- getTypeSubst
  let escape = any (`Set.notMember` fs) . typeSkolems . snd
      esc    = filter escape $ [ (v, subst theta pty)
                               | (v, pty) <- (empty, PredType ps ty) : ptys ]
      ptys   = [ (text "Variable:" <+> ppIdent v, pty)
               | (v, Value _ _ _ (ForAll _ pty)) <- localBindings vEnv ]
  mapM_ (report . errSkolemEscapingScope p m what (pp x)) esc
  return (ps, ty, x)

-- Instantiation and Generalization:
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

inst :: TypeScheme -> TCM (PredSet, Type)
inst (ForAll n (PredType ps ty)) = do
  tys <- replicateM n freshTypeVar
  return (expandAliasType tys ps, expandAliasType tys ty)

-- The function 'skol' instantiates the type of data and newtype
-- constructors in patterns. All universally quantified type variables
-- are instantiated with fresh type variables and all existentially
-- quantified type variables are instantiated with fresh skolem types.
-- All constraints that appear on the right hand side of the
-- constructor's declaration are added to the dynamic instance
-- environment.

skol :: TypeScheme -> TCM (PredSet, Type)
skol (ForAll n (PredType ps ty)) = do
  tys <- replicateM n freshTypeVar
  clsEnv <- getClassEnv
  modifyInstEnv $
    fmap $ bindSkolemInsts $ expandAliasType tys $ maxPredSet clsEnv ps
  return (emptyPredSet, expandAliasType tys ty)
  where bindSkolemInsts = flip (foldr bindSkolemInst) . Set.toList
        bindSkolemInst (Pred qcls ty') dInEnv =
          Map.insert qcls (ty' : fromMaybe [] (Map.lookup qcls dInEnv)) dInEnv

-- The function 'gen' generalizes a predicate set ps and a type tau into
-- a type scheme forall alpha . ps -> tau by universally quantifying all
-- type variables that are free in tau and not fixed by the environment.
-- The set of the latter is given by gvs.

gen :: Set.Set Int -> PredSet -> Type -> TypeScheme
gen gvs ps ty = ForAll (length tvs) (subst theta (PredType ps ty))
  where tvs = [tv | tv <- nub (typeVars ty), tv `Set.notMember` gvs]
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
  Label   _ _ _ : _ -> 1
  _ -> internalError $ "TypeCheck.varArity: " ++ show v

funType :: ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
funType m f vEnv = case qualLookupValue f vEnv of
  [Value _ _ _ tySc] -> tySc
  [Label _ _ tySc] -> tySc
  _ -> case qualLookupValue (qualQualify m f) vEnv of
    [Value _ _ _ tySc] -> tySc
    [Label _ _ tySc] -> tySc
    _ -> internalError $ "TypeCheck.funType: " ++ show f

labelType :: ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
labelType m l vEnv = case qualLookupValue l vEnv of
  [Label _ _ tySc] -> tySc
  _ -> case qualLookupValue (qualQualify m l) vEnv of
    [Label _ _ tySc] -> tySc
    _ -> internalError $ "TypeCheck.labelType: " ++ show l

-- The function 'expandPoly' handles the expansion of type aliases.

expandPoly :: QualTypeExpr -> TCM PredType
expandPoly qty = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  clsEnv <- getClassEnv
  return $ expandPolyType m tcEnv clsEnv qty

-- The function 'splitPredSet' splits a predicate set into a pair of predicate
-- set such that all type variables that appear in the types of the predicates
-- in the first predicate set are elements of a given set of type variables.

splitPredSet :: Set.Set Int -> PredSet -> (PredSet, PredSet)
splitPredSet fvs = Set.partition (all (`Set.member` fvs) . typeVars)

-- The functions 'fvEnv' and 'fsEnv' compute the set of free type variables
-- and free skolems of a type environment, respectively. We ignore the types
-- of data constructors here because we know that they are closed.

fvEnv :: ValueEnv -> Set.Set Int
fvEnv vEnv =
  Set.fromList [tv | tySc <- localTypes vEnv, tv <- typeVars tySc, tv < 0]

computeFvEnv :: TCM (Set.Set Int)
computeFvEnv = do
  theta <- getTypeSubst
  vEnv <- getValueEnv
  return $ fvEnv (subst theta vEnv)

fsEnv :: ValueEnv -> Set.Set Int
fsEnv = Set.unions . map (Set.fromList . typeSkolems) . localTypes

computeFsEnv :: TCM (Set.Set Int)
computeFsEnv = do
  theta <- getTypeSubst
  vEnv <- getValueEnv
  return $ fsEnv (subst theta vEnv)

localTypes :: ValueEnv -> [TypeScheme]
localTypes vEnv = [tySc | (_, Value _ _ _ tySc) <- localBindings vEnv]

-- ---------------------------------------------------------------------------
-- Error functions
-- ---------------------------------------------------------------------------

errPolymorphicVar :: Ident -> Message
errPolymorphicVar v = posMessage v $ hsep $ map text
  ["Variable", idName v, "has a polymorphic type"]

errTypeSigTooGeneral :: HasPosition a => a -> ModuleIdent -> Doc -> QualTypeExpr
                     -> TypeScheme -> Message
errTypeSigTooGeneral p m what qty tySc = posMessage p $ vcat
  [ text "Type signature too general", what
  , text "Inferred type:"  <+> ppTypeScheme m tySc
  , text "Type signature:" <+> ppQualTypeExpr qty
  ]

errMethodTypeTooSpecific :: HasPosition a => a -> ModuleIdent -> Doc -> PredType
                         -> TypeScheme -> Message
errMethodTypeTooSpecific p m what pty tySc = posMessage p $ vcat
  [ text "Method type too specific", what
  , text "Inferred type:" <+> ppTypeScheme m tySc
  , text "Expected type:" <+> ppPredType m pty
  ]

errNonFunctionType :: HasPosition a => a -> String -> Doc -> ModuleIdent -> Type
                   -> Message
errNonFunctionType p what doc m ty = posMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be applied"
  ]

errNonBinaryOp :: HasPosition a => a -> String -> Doc -> ModuleIdent -> Type
               -> Message
errNonBinaryOp p what doc m ty = posMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be used as binary operator"
  ]

errTypeMismatch :: HasPosition a => a -> String -> Doc -> ModuleIdent -> Type
                -> Type -> Doc -> Message
errTypeMismatch p what doc m ty1 ty2 reason = posMessage p $ vcat
  [ text "Type error in"  <+> text what, doc
  , text "Inferred type:" <+> ppType m ty2
  , text "Expected type:" <+> ppType m ty1
  , reason
  ]

errSkolemFieldLabel :: HasPosition a => a -> Ident -> Message
errSkolemFieldLabel p l = posMessage p $ hsep $ map text
  ["Existential type escapes with type of record selector", escName l]

errSkolemEscapingScope :: HasPosition a => a -> ModuleIdent -> String -> Doc
                       -> (Doc, PredType) -> Message
errSkolemEscapingScope p m what doc (whence, pty) = posMessage p $ vcat
  [ text "Existential type escapes out of its scope"
  , sep [text what <> colon, nest 2 doc], whence
  , text "Type:" <+> ppPredType m pty
  ]

errRecursiveType :: ModuleIdent -> Int -> Type -> Doc
errRecursiveType m tv ty = errIncompatibleTypes m (TypeVariable tv) ty

errIncompatibleTypes :: ModuleIdent -> Type -> Type -> Doc
errIncompatibleTypes m ty1 ty2 = sep
  [ text "Types" <+> ppType m ty1
  , nest 2 $ text "and" <+> ppType m ty2
  , text "are incompatible"
  ]

errIncompatibleLabelTypes :: HasPosition a => a -> ModuleIdent -> Ident -> Type
                          -> Type -> Message
errIncompatibleLabelTypes p m l ty1 ty2 = posMessage p $ sep
  [ text "Labeled types" <+> ppIdent l <+> text "::" <+> ppType m ty1
  , nest 10 $ text "and" <+> ppIdent l <+> text "::" <+> ppType m ty2
  , text "are incompatible"
  ]

errMissingInstance :: HasPosition a => ModuleIdent -> a -> String -> Doc -> Pred
                   -> Message
errMissingInstance m p what doc pr = posMessage p $ vcat
  [ text "Missing instance for" <+> ppPred m pr
  , text "in" <+> text what
  , doc
  ]

errAmbiguousTypeVariable :: HasPosition a => ModuleIdent -> a -> String -> Doc
                         -> PredSet -> Type -> Int -> Message
errAmbiguousTypeVariable m p what doc ps ty tv = posMessage p $ vcat
  [ text "Ambiguous type variable" <+> ppType m (TypeVariable tv)
  , text "in type" <+> ppPredType m (PredType ps ty)
  , text "inferred for" <+> text what
  , doc
  ]
