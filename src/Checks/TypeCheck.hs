{- |
    Module      :  $Header$
    Description :  Type checking Curry programs
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                                   Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2014 - 2015 Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements the type checker of the Curry compiler. The
   type checker is invoked after the syntactic correctness of the program
   has been verified. Local variables have been renamed already. Thus the
   compiler can maintain a flat type environment (which is necessary in
   order to pass the type information to later phases of the compiler).
   The type checker now checks the correct typing of all expressions and
   also verifies that the type signatures given by the user match the
   inferred types. The type checker uses the algorithm by Damas and Milner
   (1982) for inferring the types of unannotated declarations, but allows
   for polymorphic recursion when a type annotation is present.
-}
{-# LANGUAGE CPP #-}
module Checks.TypeCheck (typeCheck) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Monad              (replicateM, unless)
import qualified Control.Monad.State as S   (State, execState, gets, modify)
import           Data.List                  (nub, nubBy, partition)
import qualified Data.Map            as Map (Map, delete, empty, insert, lookup)
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set
  (Set, fromList, member, notMember, unions)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.CurryTypes (toType, toTypes, ppType, ppTypeScheme)
import Base.Expr
import Base.Messages (Message, posMessage, internalError)
import Base.SCC
import Base.TopEnv
import Base.Types
import Base.TypeSubst hiding (expandType)
import Base.Utils (foldr2)

import Env.TypeConstructor (TCEnv, TypeInfo (..), bindTypeInfo, qualLookupTC)
import Env.Value ( ValueEnv, ValueInfo (..), bindFun, rebindFun
  , bindGlobalInfo, lookupValue, qualLookupValue )

infixl 5 $-$

($-$) :: Doc -> Doc -> Doc
x $-$ y = x $$ space $$ y

-- Type checking proceeds as follows. First, the type constructor
-- environment is initialized by adding all types defined in the current
-- module. Next, the types of all data constructors and field labels
-- are entered into the type environment and then a type inference
-- for all function and value definitions is performed.
-- The type checker returns the resulting type constructor and type
-- environments.

typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> [Decl]
          -> (TCEnv, ValueEnv, [Message])
typeCheck m tcEnv tyEnv decls = execTCM check initState
  where
  check      = checkTypeSynonyms m tds &&> checkDecls
  checkDecls = do
    bindTypes tds
    bindConstrs
    mapM_ checkFieldLabel tds &&> bindLabels
    tcDecls vds
  (tds, vds) = partition isTypeDecl decls
  initState  = TcState m tcEnv tyEnv idSubst emptySigEnv 0 []

-- The type checker makes use of a state monad in order to maintain the type
-- environment, the current substitution, and a counter which is used for
-- generating fresh type variables.

data TcState = TcState
  { moduleIdent :: ModuleIdent -- read only
  , tyConsEnv   :: TCEnv
  , valueEnv    :: ValueEnv
  , typeSubst   :: TypeSubst
  , sigEnv      :: SigEnv
  , nextId      :: Int         -- automatic counter
  , errors      :: [Message]
  }

type TCM = S.State TcState

getModuleIdent :: TCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getTyConsEnv :: TCM TCEnv
getTyConsEnv = S.gets tyConsEnv

setTyConsEnv :: TCEnv -> TCM ()
setTyConsEnv tcEnv = S.modify $ \ s -> s { tyConsEnv = tcEnv }

getValueEnv :: TCM ValueEnv
getValueEnv = S.gets valueEnv

modifyValueEnv :: (ValueEnv -> ValueEnv) -> TCM ()
modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

getTypeSubst :: TCM TypeSubst
getTypeSubst = S.gets typeSubst

modifyTypeSubst :: (TypeSubst -> TypeSubst) -> TCM ()
modifyTypeSubst f = S.modify $ \ s -> s { typeSubst = f $ typeSubst s }

getSigEnv :: TCM SigEnv
getSigEnv = S.gets sigEnv

modifySigEnv :: (SigEnv -> SigEnv) -> TCM ()
modifySigEnv f = S.modify $ \ s -> s { sigEnv = f $ sigEnv s }

getNextId :: TCM Int
getNextId = do
  nid <- S.gets nextId
  S.modify $ \ s -> s { nextId = succ nid }
  return nid

report :: Message -> TCM ()
report err = S.modify $ \ s -> s { errors = err : errors s }

(&&>) :: TCM () -> TCM () -> TCM ()
pre &&> suf = do
  errs <- pre >> S.gets errors
  if null errs then suf else return ()

execTCM :: TCM a -> TcState -> (TCEnv, ValueEnv, [Message])
execTCM tcm s = let s' = S.execState tcm s
                in  ( tyConsEnv s'
                    , typeSubst s' `subst` valueEnv s'
                    , reverse $ errors s'
                    )

-- Defining Types:
-- Before type checking starts, the types defined in the local module
-- have to be entered into the type constructor environment. All type
-- synonyms occurring in the definitions are fully expanded (except for
-- record types) and all type constructors are qualified with the name
-- of the module in which they are defined. This is possible because
-- Curry does not allow (mutually) recursive type synonyms.
-- In order to simplify the expansion of type synonyms, the compiler
-- first performs a dependency analysis on the type definitions.
-- This also makes it easy to identify (mutually) recursive synonyms.

-- Note that 'bindTC' is passed the final type constructor environment in
-- order to handle the expansion of type synonyms. This does not lead to a
-- termination problem because 'checkTypeDecls' already has checked that there
-- are no recursive type synonyms.

-- We have to be careful with existentially quantified type variables for
-- data constructors. An existentially quantified type variable may
-- shadow a universally quantified variable from the left hand side of
-- the type declaration. In order to avoid wrong indices being assigned
-- to these variables, we replace all shadowed variables in the left hand
-- side by anonId before passing them to 'expandMonoType' and
-- 'expandMonoTypes', respectively.

checkTypeSynonyms :: ModuleIdent -> [Decl] -> TCM ()
checkTypeSynonyms m = mapM_ (checkTypeDecls m) . scc bound free
  where
  bound (DataDecl    _ tc _ _) = [tc]
  bound (NewtypeDecl _ tc _ _) = [tc]
  bound (TypeDecl    _ tc _ _) = [tc]
  bound _                      = []
  free  (DataDecl     _ _ _ _) = []
  free  (NewtypeDecl  _ _ _ _) = []
  free  (TypeDecl    _ _ _ ty) = ft m ty []
  free _                       = []

checkTypeDecls :: ModuleIdent -> [Decl] -> TCM ()
checkTypeDecls _ []                    =
  internalError "TypeCheck.checkTypeDecls: empty list"
checkTypeDecls _ [DataDecl    _ _ _ _] = return ()
checkTypeDecls _ [NewtypeDecl _ _ _ _] = return ()
checkTypeDecls m [TypeDecl  _ tc _ ty]
  | tc `elem` ft m ty [] = report $ errRecursiveTypes [tc]
  | otherwise            = return ()
checkTypeDecls _ (TypeDecl _ tc _ _ : ds) =
      report $ errRecursiveTypes $ tc : [tc' | TypeDecl _ tc' _ _ <- ds]
checkTypeDecls _ _                     =
  internalError "TypeCheck.checkTypeDecls: no type synonym"

ft :: ModuleIdent -> TypeExpr -> [Ident] -> [Ident]
ft m (ConstructorType tc tys) tcs =
  maybe id (:) (localIdent m tc) (foldr (ft m) tcs tys)
ft _ (VariableType         _) tcs = tcs
ft m (TupleType          tys) tcs = foldr (ft m) tcs tys
ft m (ListType            ty) tcs = ft m ty tcs
ft m (ArrowType      ty1 ty2) tcs = ft m ty1 $ ft m ty2 $ tcs
ft m (ParenType           ty) tcs = ft m ty tcs

-- When a field label occurs in more than one constructor declaration of
-- a data type, the compiler ensures that the label is defined
-- consistently, i.e. both occurrences have the same type. In addition,
-- the compiler ensures that no existentially quantified type variable occurs
-- in the type of a field label because such type variables necessarily escape
-- their scope with the type of the record selection function associated with
-- the field label.

checkFieldLabel :: Decl -> TCM ()
checkFieldLabel (DataDecl _ _ tvs cs) = do
  ls' <- mapM (tcFieldLabel tvs) labels
  mapM_ tcFieldLabels (groupLabels ls')
  where labels = [(l, p, ty) | RecordDecl _ _ _ fs <- cs,
                               FieldDecl p ls ty <- fs, l <- ls]
checkFieldLabel (NewtypeDecl _ _ tvs (NewRecordDecl p _ _ (l,ty))) = do
  _ <- tcFieldLabel tvs (l, p, ty)
  return ()
checkFieldLabel _ = return ()

tcFieldLabel :: [Ident] -> (Ident, Position, TypeExpr)
             -> TCM (Ident, Position, Type)
tcFieldLabel tvs (l, p, ty) = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  let ForAll n ty' = polyType $ expandMonoType' m tcEnv tvs ty
      what         = text "record selection"
  if n <= length tvs then return (l, p, ty')
                     else do report $ errSkolemEscapingScope p m what ty'
                             return (l, p, ty')

groupLabels :: Eq a => [(a,b,c)] -> [(a,b,[c])]
groupLabels []             = []
groupLabels ((x,y,z):xyzs) =
  (x,y,z:map thrd3 xyzs') : groupLabels xyzs''
  where (xyzs',xyzs'') = partition ((x ==) . fst3) xyzs
        fst3  (a,_,_) = a
        thrd3 (_,_,c) = c

tcFieldLabels :: (Ident, Position, [Type]) -> TCM ()
tcFieldLabels (_,_,[])     = return ()
tcFieldLabels (l,p,ty:tys) = do
  m <- getModuleIdent
  unless (null (filter (ty /=) tys)) $
    report $ errIncompatibleLabelTypes p m l ty (head tys)

-- The type constructor environment 'tcEnv' maintains all types
-- in fully expanded form.
bindTypes :: [Decl] -> TCM ()
bindTypes ds = do
  m      <- getModuleIdent
  tcEnv  <- getTyConsEnv
  let tcEnv'  = foldr (bindTC m tcEnv') tcEnv ds
  setTyConsEnv tcEnv'

bindTC :: ModuleIdent -> TCEnv -> Decl -> TCEnv -> TCEnv
bindTC m tcEnv (DataDecl _ tc tvs cs) =
  bindTypeInfo DataType m tc tvs (map mkData cs)
  where
  mkData (ConstrDecl _ evs     c  tys) = mkData' evs c  tys
  mkData (ConOpDecl  _ evs ty1 op ty2) = mkData' evs op [ty1, ty2]
  mkData (RecordDecl _ evs       c fs) =
    let (labels, tys) = unzip [(l ,ty) | FieldDecl _ ls ty <- fs, l <- ls]
    in mkRec evs c labels tys
  mkData' evs c tys = DataConstr c (length evs) $
    expandMonoTypes m tcEnv (cleanTVars tvs evs) tys
  mkRec evs c ls tys = RecordConstr c (length evs) ls $
    expandMonoTypes m tcEnv (cleanTVars tvs evs) tys
bindTC m tcEnv (NewtypeDecl _ tc tvs (NewConstrDecl _ evs c ty)) =
  bindTypeInfo RenamingType m tc tvs (DataConstr c (length evs) [ty'])
  where ty' = expandMonoType' m tcEnv (cleanTVars tvs evs) ty
bindTC m tcEnv (NewtypeDecl _ tc tvs (NewRecordDecl _ evs c (l, ty))) =
  bindTypeInfo RenamingType m tc tvs (RecordConstr c (length evs) [l] [ty'])
  where ty' = expandMonoType' m tcEnv (cleanTVars tvs evs) ty
bindTC m tcEnv (TypeDecl _ tc tvs ty) =
  bindTypeInfo AliasType m tc tvs (expandMonoType' m tcEnv tvs ty)
bindTC _ _ _ = id

cleanTVars :: [Ident] -> [Ident] -> [Ident]
cleanTVars tvs evs = [if tv `elem` evs then anonId else tv | tv <- tvs]

-- Defining Data Constructors:
-- In the next step, the types of all data constructors are entered into
-- the type environment using the information just entered into the type
-- constructor environment. Thus, we can be sure that all type variables
-- have been properly renamed and all type synonyms are already expanded.

bindConstrs :: TCM ()
bindConstrs = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindConstrs' m tcEnv

bindConstrs' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindConstrs' m tcEnv tyEnv = foldr (bindData . snd) tyEnv
                           $ localBindings tcEnv
  where
  bindData (DataType tc n cs) tyEnv' =
    foldr (bindConstr m n (constrType' tc n)) tyEnv' cs
  bindData (RenamingType tc n c) tyEnv' =
    bindNewConstr m n (constrType' tc n) c tyEnv'
  bindData (AliasType _ _ _) tyEnv' = tyEnv'
  bindConstr m' n ty (DataConstr c n' tys) =
    bindGlobalInfo (\qc tyScheme -> DataConstructor qc arity ls tyScheme) m' c
                   (ForAllExist n n' (foldr TypeArrow ty tys))
    where arity = length tys
          ls    = replicate arity anonId
  bindConstr m' n ty (RecordConstr c n' ls tys) =
    bindGlobalInfo (\qc tyScheme -> DataConstructor qc arity ls tyScheme) m' c
                   (ForAllExist n n' (foldr TypeArrow ty tys))
    where arity = length tys
  bindNewConstr m' n cty (DataConstr c n' [lty]) =
    bindGlobalInfo (\qc tyScheme -> NewtypeConstructor qc anonId tyScheme) m' c
                   (ForAllExist n n' (TypeArrow lty cty))
  bindNewConstr m' n cty (RecordConstr c n' [l] [lty]) =
    bindGlobalInfo (\qc tyScheme -> NewtypeConstructor qc l tyScheme) m' c
                   (ForAllExist n n' (TypeArrow lty cty))
  bindNewConstr _ _ _ _ =
    internalError "TypeCheck.bindConstrs: newtype with illegal constructors"
  constrType' tc n = TypeConstructor tc $ map TypeVariable [0 .. n - 1]

-- Defining Field Labels:
-- Next the types of all field labels are added to the type environment.
-- Since we use the type constructor environment again,
-- we can be sure that all type variables have been properly renamed
-- and all type synonyms are already expanded.

bindLabels :: TCM ()
bindLabels = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  modifyValueEnv $ bindLabels' m tcEnv

bindLabels' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
bindLabels' m tcEnv tyEnv = foldr (bindData . snd) tyEnv
                          $ localBindings tcEnv
  where
  bindData (DataType tc n cs) tyEnv' =
    foldr (bindLabel m n (constrType' tc n)) tyEnv' $ nubBy sameLabel clabels
    where
      labels   = zip (concatMap recLabels cs) (concatMap recLabelTypes cs)
      clabels  = [(l, constr l, ty) | (l, ty) <- labels]
      constr l = map (qualifyLike tc) $
        [constrIdent c | c <- cs, l `elem` recLabels c]
      sameLabel (l1,_,_) (l2,_,_) = l1 == l2
  bindData (RenamingType tc n (RecordConstr c _ [l] [lty])) tyEnv' =
    bindLabel m n (constrType' tc n) (l, [qc], lty) tyEnv'
    where
      qc = qualifyLike tc c
  bindData (RenamingType _ _ (RecordConstr _ _ _ _)) _ = internalError $
    "Checks.TypeCheck.bindLabels: RenamingType with more than one record label"
  bindData (RenamingType _ _ (DataConstr _ _ _)) tyEnv' = tyEnv'
  bindData (AliasType _ _ _) tyEnv' = tyEnv'
  bindLabel m' n ty (l, lcs, lty) =
    bindGlobalInfo (\qc tyScheme -> Label qc lcs tyScheme) m' l
                   (ForAll n (TypeArrow ty lty))
  constrType' tc n = TypeConstructor tc $ map TypeVariable [0 .. n - 1]

-- Type Signatures:
-- The type checker collects type signatures in a flat environment. All
-- anonymous variables occurring in a signature are replaced by fresh
-- names. However, the type is not expanded so that the signature is
-- available for use in the error message that is printed when the
-- inferred type is less general than the signature.

type SigEnv = Map.Map Ident TypeExpr

emptySigEnv :: SigEnv
emptySigEnv = Map.empty

unbindTypeSig :: Ident -> SigEnv -> SigEnv
unbindTypeSig = Map.delete

bindTypeSig :: Ident -> TypeExpr -> SigEnv -> SigEnv
bindTypeSig = Map.insert

bindTypeSigs :: Decl -> SigEnv -> SigEnv
bindTypeSigs (TypeSig _ vs ty) env =
  foldr (flip bindTypeSig (nameSigType ty)) env vs
bindTypeSigs _                 env = env

lookupTypeSig :: Ident -> SigEnv -> Maybe TypeExpr
lookupTypeSig = Map.lookup

qualLookupTypeSig :: ModuleIdent -> QualIdent -> SigEnv -> Maybe TypeExpr
qualLookupTypeSig m f sigs = localIdent m f >>= flip lookupTypeSig sigs

nameSigType :: TypeExpr -> TypeExpr
nameSigType ty = fst $ nameType ty $ filter (`notElem` fv ty) identSupply

nameTypes :: [TypeExpr] -> [Ident] -> ([TypeExpr], [Ident])
nameTypes []         tvs = ([]        , tvs  )
nameTypes (ty : tys) tvs = (ty' : tys', tvs'')
  where (ty' , tvs' ) = nameType ty tvs
        (tys', tvs'') = nameTypes tys tvs'

nameType :: TypeExpr -> [Ident] -> (TypeExpr, [Ident])
nameType (ConstructorType tc tys) tvs = (ConstructorType tc tys', tvs')
  where (tys', tvs') = nameTypes tys tvs
nameType (VariableType tv) (tv' : tvs)
  | isAnonId tv = (VariableType tv', tvs      )
  | otherwise   = (VariableType tv , tv' : tvs)
nameType (TupleType tys) tvs = (TupleType tys', tvs')
  where (tys', tvs') = nameTypes tys tvs
nameType (ListType ty) tvs = (ListType ty', tvs')
  where (ty', tvs') = nameType ty tvs
nameType (ArrowType ty1 ty2) tvs = (ArrowType ty1' ty2', tvs'')
  where (ty1', tvs' ) = nameType ty1 tvs
        (ty2', tvs'') = nameType ty2 tvs'
nameType (VariableType _) [] = internalError
 "TypeCheck.nameType: empty ident list"
nameType (ParenType ty) tvs = (ParenType ty', tvs')
  where (ty', tvs') = nameType ty tvs

-- Type Inference:
-- Before type checking a group of declarations, a dependency analysis is
-- performed and the declaration group is eventually transformed into
-- nested declaration groups which are checked separately. Within each
-- declaration group, first the left hand sides of all declarations are
-- typed. Next, the right hand sides of the declarations are typed in the
-- extended type environment. Finally, the types for the left and right
-- hand sides are unified and the types of all defined functions are
-- generalized. The generalization step will also check that the type
-- signatures given by the user match the inferred types.

-- Argument and result types of foreign functions using the ccall calling
-- convention are restricted to the basic types Bool, Char, Int, and Float.
-- In addition, IO t is a legitimate result type when t is either one of the
-- basic types or ().

-- TODO: Extend the set of legitimate types to match the types admitted
-- by the Haskell Foreign Function Interface Addendum.

tcDecls :: [Decl] -> TCM ()
tcDecls ds = do
  m <- getModuleIdent
  oldSig <- getSigEnv
  modifySigEnv $ \ sigs -> foldr bindTypeSigs sigs ods
  mapM_ tcDeclGroup $ scc bv (qfv m) vds
  modifySigEnv (const oldSig)
  where (vds, ods) = partition isValueDecl ds

tcDeclGroup :: [Decl] -> TCM ()
tcDeclGroup [ForeignDecl _ _ _ f ty] = tcForeign f ty
tcDeclGroup [ExternalDecl      _ fs] = mapM_ tcExternal fs
tcDeclGroup [FreeDecl          _ vs] = mapM_ tcFree     vs
tcDeclGroup ds                       = do
  tyEnv0 <- getValueEnv
  tysLhs <- mapM tcDeclLhs ds
  tysRhs <- mapM (tcDeclRhs tyEnv0) ds
  sequence_ (zipWith3 unifyDecl ds tysLhs tysRhs)
  theta <- getTypeSubst
  mapM_ (genDecl (fvEnv (subst theta tyEnv0)) theta) ds
--tcDeclGroup m tcEnv _ [ForeignDecl p cc _ f ty] =
--  tcForeign m tcEnv p cc f ty

--tcForeign :: ModuleIdent -> TCEnv -> Position -> CallConv -> Ident
--               -> TypeExpr -> TCM ()
--tcForeign m tcEnv p cc f ty =
--  S.modify (bindFun m f (checkForeignType cc (expandPolyType tcEnv ty)))
--  where checkForeignType CallConvPrimitive ty = ty
--        checkForeignType CallConvCCall (ForAll n ty) =
--          ForAll n (checkCCallType ty)
--        checkCCallType (TypeArrow ty1 ty2)
--          | isCArgType ty1 = TypeArrow ty1 (checkCCallType ty2)
--          | otherwise = errorAt p (invalidCType "argument" m ty1)
--        checkCCallType ty
--          | isCResultType ty = ty
--          | otherwise = errorAt p (invalidCType "result" m ty)
--        isCArgType (TypeConstructor tc []) = tc `elem` basicTypeId
--        isCArgType _ = False
--        isCResultType (TypeConstructor tc []) = tc `elem` basicTypeId
--        isCResultType (TypeConstructor tc [ty]) =
--          tc == qIOId && (ty == unitType || isCArgType ty)
--        isCResultType _ = False
--        basicTypeId = [qBoolId,qCharId,qIntId,qFloatId]

tcForeign :: Ident -> TypeExpr -> TCM ()
tcForeign f ty = do
  m <- getModuleIdent
  tySc@(ForAll _ ty') <- expandPolyType ty
  modifyValueEnv $ bindFun m f (arrowArity ty') tySc

tcExternal :: Ident -> TCM ()
tcExternal f = do
  sigs <- getSigEnv
  case lookupTypeSig f sigs of
    Nothing -> internalError "TypeCheck.tcExternal"
    Just ty -> tcForeign f ty

tcFree :: Ident -> TCM ()
tcFree v = do
  sigs <- getSigEnv
  ty <- case lookupTypeSig v sigs of
    Nothing -> freshTypeVar
    Just t  -> do
      ForAll n ty' <- expandPolyType t
      if (n == 0) then return ty' else do
        -- because of error aggregation, we have to fix
        -- the corrupt information
        report $ errPolymorphicFreeVar v
        modifySigEnv $ unbindTypeSig v
        freshTypeVar
  m  <- getModuleIdent
  modifyValueEnv $ bindFun m v (arrowArity ty) $ monoType ty

tcDeclLhs :: Decl -> TCM Type
tcDeclLhs (FunctionDecl _ f _) = tcFunDecl f
tcDeclLhs (PatternDecl  p t _) = tcPattern p t
tcDeclLhs _ = internalError "TypeCheck.tcDeclLhs: no pattern match"

tcFunDecl :: Ident -> TCM Type
tcFunDecl v = do
  sigs <- getSigEnv
  m <- getModuleIdent
  ty <- case lookupTypeSig v sigs of
    Nothing -> freshTypeVar
    Just t  -> expandPolyType t >>= inst
  modifyValueEnv $ bindFun m v (arrowArity ty) (monoType ty)
  return ty

tcDeclRhs :: ValueEnv -> Decl -> TCM Type
tcDeclRhs tyEnv0 (FunctionDecl _ f (eq:eqs)) = do
  tcEquation tyEnv0 eq >>= flip tcEqns eqs
  where tcEqns ty [] = return ty
        tcEqns ty (eq1@(Equation p _ _):eqs1) = do
          tcEquation tyEnv0 eq1 >>=
            unify p "equation" (ppDecl (FunctionDecl p f [eq1])) ty >>
            tcEqns ty eqs1
tcDeclRhs tyEnv0 (PatternDecl _ _ rhs) = tcRhs tyEnv0 rhs
tcDeclRhs _ _ = internalError "TypeCheck.tcDeclRhs: no pattern match"

unifyDecl :: Decl -> Type -> Type -> TCM ()
unifyDecl (FunctionDecl p f _) =
  unify p "function binding" (text "Function:" <+> ppIdent f)
unifyDecl (PatternDecl  p t _) =
  unify p "pattern binding" (ppPattern 0 t)
unifyDecl _ = internalError "TypeCheck.unifyDecl: no pattern match"

-- In Curry we cannot generalize the types of let-bound variables because
-- they can refer to logic variables. Without this monomorphism
-- restriction unsound code like
--
-- bug = x =:= 1 & x =:= 'a'
--   where x :: a
--         x = fresh
-- fresh :: a
-- fresh = x where x free
--
-- could be written. Note that fresh has the polymorphic type
-- forall alpha . alpha. This is correct because fresh is a
-- function and therefore returns a different variable at each
-- invocation.

-- The code in 'genVar' below also verifies that the inferred type
-- for a variable or function matches the type declared in a type
-- signature. As the declared type is already used for assigning an initial
-- type to a variable when it is used, the inferred type can only be more
-- specific. Therefore, if the inferred type does not match the type
-- signature the declared type must be too general.

genDecl :: Set.Set Int -> TypeSubst -> Decl -> TCM ()
genDecl lvs theta (FunctionDecl _ f (Equation _ lhs _ : _)) =
  genVar True lvs theta arity f
  where arity = Just $ length $ snd $ flatLhs lhs
genDecl lvs theta (PatternDecl  _ t   _) =
  mapM_ (genVar False lvs theta Nothing) (bv t)
genDecl _ _ _ = internalError "TypeCheck.genDecl: no pattern match"

genVar :: Bool -> Set.Set Int -> TypeSubst -> Maybe Int -> Ident -> TCM ()
genVar poly lvs theta ma v = do
  sigs <- getSigEnv
  m <- getModuleIdent
  tyEnv <- getValueEnv
  let sigma = genType poly $ subst theta $ varType v tyEnv
      arity  = fromMaybe (varArity v tyEnv) ma
  case lookupTypeSig v sigs of
    Nothing    -> modifyValueEnv $ rebindFun m v arity sigma
    Just sigTy -> do
      sigma' <- expandPolyType sigTy
      unless (eqTyScheme sigma sigma') $ report
        $ errTypeSigTooGeneral (idPosition v) m what sigTy sigma
      modifyValueEnv $ rebindFun m v arity sigma
  where
  what = text (if poly then "Function:" else "Variable:") <+> ppIdent v
  genType poly' (ForAll n ty)
    | n > 0     = internalError $ "TypeCheck.genVar: "
                    ++ showLine (idPosition v) ++ show v ++ " :: " ++ show ty
    | poly'     = gen lvs ty
    | otherwise = monoType ty
  eqTyScheme (ForAll _ t1) (ForAll _ t2) = equTypes t1 t2

tcEquation :: ValueEnv -> Equation -> TCM Type
tcEquation tyEnv0 (Equation p lhs rhs) = do
  tys <- mapM (tcPattern p) ts
  ty <- tcRhs tyEnv0 rhs
  checkSkolems p (text "Function: " <+> ppIdent f) tyEnv0
                 (foldr TypeArrow ty tys)
  where (f, ts) = flatLhs lhs

tcLiteral :: Literal -> TCM Type
tcLiteral (Char   _ _) = return charType
tcLiteral (Int    v _)  = do --return intType
  m  <- getModuleIdent
  ty <- freshConstrained [intType, floatType]
  modifyValueEnv $ bindFun m v (arrowArity ty) $ monoType ty
  return ty
tcLiteral (Float  _ _) = return floatType
tcLiteral (String _ _) = return stringType

tcPattern :: Position -> Pattern -> TCM Type
tcPattern _ (LiteralPattern    l) = tcLiteral l
tcPattern _ (NegativePattern _ l) = tcLiteral l
tcPattern _ (VariablePattern   v) = do
  sigs <- getSigEnv
  ty <- case lookupTypeSig v sigs of
    Nothing -> freshTypeVar
    Just t  -> expandPolyType t >>= inst
  tyEnv <- getValueEnv
  m <- getModuleIdent
  maybe (modifyValueEnv (bindFun m v (arrowArity ty) (monoType ty))
           >> return ty)
        (\ (ForAll _ t) -> return t)
        (sureVarType v tyEnv)
tcPattern p t@(ConstructorPattern c ts) = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  ty <- skol $ constrType m c tyEnv
  unifyArgs (ppPattern 0 t) ts ty
  where
  unifyArgs _   []       ty                  = return ty
  unifyArgs doc (t1:ts1) (TypeArrow ty1 ty2) = do
    ty' <- tcPattern p t1
    unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1) ty1 ty'
    unifyArgs doc ts1 ty2
  unifyArgs _ _ _ = internalError "TypeCheck.tcPattern"
tcPattern p (InfixPattern t1 op t2) = tcPattern p
                                    $ ConstructorPattern op [t1, t2]
tcPattern p (ParenPattern        t) = tcPattern p t
tcPattern _ r@(RecordPattern  c fs) = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  ty    <- arrowBase <$> skol (constrType m c tyEnv)
  mapM_ (tcField tcPattern "pattern" doc ty) fs
  return ty
  where doc t1 = ppPattern 0 r $-$ text "Term:" <+> ppPattern 0 t1
tcPattern p (TuplePattern _ ts)
 | null ts   = return unitType
 | otherwise = tupleType <$> mapM (tcPattern p) ts
tcPattern p t@(ListPattern _ ts) =
  freshTypeVar >>= flip (tcElems (ppPattern 0 t)) ts
  where
  tcElems _   ty []       = return (listType ty)
  tcElems doc ty (t1:ts1) = do
    ty' <- tcPattern p t1
    unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1) ty ty'
    tcElems doc ty ts1
tcPattern p t@(AsPattern v t') = do
  ty1 <- tcPattern p (VariablePattern v)
  ty2 <- tcPattern p t'
  unify p "pattern" (ppPattern 0 t) ty1 ty2
  return ty1
tcPattern p (LazyPattern        _ t) = tcPattern p t
tcPattern p t@(FunctionPattern f ts) = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  ty <- inst (funType m f tyEnv)
  unifyArgs (ppPattern 0 t) ts ty
  where
  unifyArgs _   []       ty                  = return ty
  unifyArgs doc (t1:ts1) (TypeArrow ty1 ty2) = do
    ty' <- tcPattern p t1
    unify p "function pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1) ty1 ty'
    unifyArgs doc ts1 ty2
  unifyArgs doc (t1:ts1) ty                  = do
    (a, b) <- tcArrow p "function pattern" doc ty
    ty'    <- tcPattern p t1
    unify p "function pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1) ty' a
    unifyArgs doc ts1 b
tcPattern p (InfixFuncPattern t1 op t2) = tcPattern p
                                        $ FunctionPattern op [t1, t2]

tcRhs ::ValueEnv -> Rhs -> TCM Type
tcRhs tyEnv0 (SimpleRhs p e ds) = do
  tcDecls ds
  ty <- tcExpr p e
  checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 ty
tcRhs tyEnv0 (GuardedRhs es ds) = do
  tcDecls ds
  tcCondExprs tyEnv0 es

tcCondExprs :: ValueEnv -> [CondExpr] -> TCM Type
tcCondExprs tyEnv0 es = do
  let gty = boolType -- the type of conditions
  ty <- freshTypeVar
  mapM_ (tcCondExpr gty ty) es
  return ty
  where
  tcCondExpr gty ty (CondExpr p g e) = do
    tcExpr p g >>= unify p "guard" (ppExpr 0 g) gty
    tcExpr p e >>= checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0
               >>= unify p "guarded expression" (ppExpr 0 e) ty

tcExpr :: Position -> Expression -> TCM Type
tcExpr _ (Literal     l) = tcLiteral l
tcExpr _ (Variable    v)
  | isAnonId v' = do -- anonymous free variable
    m <- getModuleIdent
    ty <- freshTypeVar
    modifyValueEnv $ bindFun m v' (arrowArity ty) $ monoType ty
    return ty
  | otherwise   = do
    sigs <- getSigEnv
    m <- getModuleIdent
    case qualLookupTypeSig m v sigs of
      Just ty -> expandPolyType ty >>= inst
      Nothing -> getValueEnv >>= inst . funType m v
  where v' = unqualify v
tcExpr _ (Constructor c) = do
  m <- getModuleIdent
  getValueEnv >>= instExist . constrType m c
tcExpr p (Typed   e sig) = do
  m <- getModuleIdent
  tyEnv0 <- getValueEnv
  ty <- tcExpr p e
  sigma' <- expandPolyType sig'
  inst sigma' >>= flip (unify p "explicitly typed expression" (ppExpr 0 e)) ty
  theta <- getTypeSubst
  let sigma  = gen (fvEnv (subst theta tyEnv0)) (subst theta ty)
  unless (sigma == sigma') $ report $
    errTypeSigTooGeneral p m (text "Expression:" <+> ppExpr 0 e) sig' sigma
  return ty
  where sig' = nameSigType sig
tcExpr p (Paren       e) = tcExpr p e
tcExpr _ r@(Record c fs) = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  ty    <- arrowBase <$> instExist (constrType m c tyEnv)
  mapM_ (tcField tcExpr "construction" doc ty) fs
  return ty
  where doc e1 = ppExpr 0 r $-$ text "Term:" <+> ppExpr 0 e1
tcExpr p r@(RecordUpdate e fs) = do
  ty <- tcExpr p e
  mapM_ (tcField tcExpr "update" doc ty) fs
  return ty
  where doc e1 = ppExpr 0 r $-$ text "Term:" <+> ppExpr 0 e1
tcExpr p (Tuple _ es)
  | null es   = return unitType
  | otherwise = tupleType <$> mapM (tcExpr p) es
tcExpr p e@(List _ es) = freshTypeVar >>= tcElems (ppExpr 0 e) es
  where tcElems _   []       ty = return (listType ty)
        tcElems doc (e1:es1) ty =
          tcExpr p e1 >>=
          unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e1)
                ty >>
          tcElems doc es1 ty
tcExpr p (ListCompr _ e qs) = do
  tyEnv0 <- getValueEnv
  mapM_ (tcQual p) qs
  ty <- tcExpr p e
  checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (listType ty)
tcExpr p e@(EnumFrom             e1) = do
  tcEnum p e e1
  return (listType intType)
tcExpr p e@(EnumFromThen      e1 e2) = do
  mapM_ (tcEnum p e) [e1, e2]
  return (listType intType)
tcExpr p e@(EnumFromTo        e1 e2) = do
  mapM_ (tcEnum p e) [e1, e2]
  return (listType intType)
tcExpr p e@(EnumFromThenTo e1 e2 e3) = do
  mapM_ (tcEnum p e) [e1, e2, e3]
  return (listType intType)
tcExpr p e@(UnaryMinus op e1) = do
  opTy <- opType op
  ty1 <- tcExpr p e1
  unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
        opTy ty1
  return ty1
  where opType op'
          | op' == minusId  = freshConstrained [intType,floatType]
          | op' == fminusId = return floatType
          | otherwise = internalError $ "TypeCheck.tcExpr unary " ++ idName op'
tcExpr p e@(Apply e1 e2) = do
  ty1 <- tcExpr p e1
  ty2 <- tcExpr p e2
  (alpha,beta) <-
    tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
           ty1
  unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
        alpha ty2
  return beta
tcExpr p e@(InfixApply e1 op e2) = do
  opTy <- tcExpr p (infixOp op)
  ty1  <- tcExpr p e1
  ty2  <- tcExpr p e2
  (alpha,beta,gamma) <-
    tcBinary p "infix application"
             (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) opTy
  unify p "infix application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
        alpha ty1
  unify p "infix application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
        beta ty2
  return gamma
tcExpr p e@(LeftSection e1 op) = do
  opTy <- tcExpr p (infixOp op)
  ty1  <- tcExpr p e1
  (alpha,beta) <-
    tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
            opTy
  unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
        alpha ty1
  return beta
tcExpr p e@(RightSection op e1) = do
  opTy <- tcExpr p (infixOp op)
  ty1  <- tcExpr p e1
  (alpha,beta,gamma) <-
    tcBinary p "right section"
             (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) opTy
  unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
        beta ty1
  return (TypeArrow alpha gamma)
tcExpr p expr@(Lambda _ ts e) = do
  tyEnv0 <- getValueEnv
  tys <- mapM (tcPattern p) ts
  ty <- tcExpr p e
  checkSkolems p (text "Expression:" <+> ppExpr 0 expr) tyEnv0
               (foldr TypeArrow ty tys)
tcExpr p (Let ds e) = do
  tyEnv0 <- getValueEnv
  tcDecls ds
  ty <- tcExpr p e
  checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 ty
tcExpr p (Do sts e) = do
  tyEnv0 <- getValueEnv
  mapM_ (tcStmt p) sts
  alpha <- freshTypeVar
  ty <- tcExpr p e
  unify p "statement" (ppExpr 0 e) (ioType alpha) ty
  checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 ty
tcExpr p e@(IfThenElse _ e1 e2 e3) = do
  ty1 <- tcExpr p e1
  unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
        boolType ty1
  ty2 <- tcExpr p e2
  ty3 <- tcExpr p e3
  unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
        ty2 ty3
  return ty3
tcExpr p (Case _ _ e alts) = do
  tyEnv0 <- getValueEnv
  ty <- tcExpr p e
  alpha <- freshTypeVar
  tcAlts tyEnv0 ty alpha alts
  where
  tcAlts _      _   ty  []           = return ty
  tcAlts tyEnv0 ty1 ty2 (alt1:alts1) = do
    tcAlt (ppAlt alt1) tyEnv0 ty1 ty2 alt1
    tcAlts tyEnv0 ty1 ty2 alts1
  tcAlt doc tyEnv0 ty1 ty2 (Alt p1 t rhs) = do
    ty' <- tcPattern p1 t
    unify p1 "case pattern" (doc $-$ text "Term:" <+> ppPattern 0 t) ty1 ty'
    tcRhs tyEnv0 rhs >>= unify p1 "case branch" doc ty2

tcEnum :: Position -> Expression -> Expression -> TCM ()
tcEnum p e e1 = do
  ty1 <- tcExpr p e1
  unify p "arithmetic sequence" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
    intType ty1

tcQual :: Position -> Statement -> TCM ()
tcQual p (StmtExpr     _ e) =
  tcExpr p e >>= unify p "guard" (ppExpr 0 e) boolType
tcQual p q@(StmtBind _ t e) = do
  ty1 <- tcPattern p t
  ty2 <- tcExpr p e
  unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
        (listType ty1) ty2
tcQual _ (StmtDecl      ds) = tcDecls ds

tcStmt ::Position -> Statement -> TCM ()
tcStmt p (StmtExpr _ e) = do
  alpha <- freshTypeVar
  ty    <- tcExpr p e
  unify p "statement" (ppExpr 0 e) (ioType alpha) ty
tcStmt p st@(StmtBind _ t e) = do
  ty1 <- tcPattern p t
  ty2 <- tcExpr p e
  unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
    (ioType ty1) ty2
tcStmt _ (StmtDecl ds) = tcDecls ds

tcField :: (Position -> a -> TCM Type) -> String -> (a -> Doc) -> Type
        -> Field a -> TCM Type
tcField tcheck what doc ty (Field p l x) = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  TypeArrow ty1 ty2 <- inst (labelType m l tyEnv)
  unify p "field label" empty ty ty1
  lty <- tcheck p x
  unify p ("record " ++ what) (doc x) ty2 lty
  return lty

-- The function 'tcArrow' checks that its argument can be used as
-- an arrow type a -> b and returns the pair (a,b).
tcArrow :: Position -> String -> Doc -> Type -> TCM (Type, Type)
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
tcBinary :: Position -> String -> Doc -> Type -> TCM (Type, Type, Type)
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
unify :: Position -> String -> Doc -> Type -> Type -> TCM ()
unify p what doc ty1 ty2 = do
  theta <- getTypeSubst
  let ty1' = subst theta ty1
  let ty2' = subst theta ty2
  m     <- getModuleIdent
  case unifyTypes m ty1' ty2' of
    Left reason -> report $ errTypeMismatch p what doc m ty1' ty2' reason
    Right sigma -> modifyTypeSubst (compose sigma)

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
unifyTypes m (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
  | tc1 == tc2 = unifyTypeLists m tys1 tys2
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
  unifyTypesTheta theta = either Left (Right . flip compose theta)
                          (unifyTypes m (subst theta ty1) (subst theta ty2))

-- For each declaration group, the type checker has to ensure that no
-- skolem type escapes its scope.
checkSkolems :: Position -> Doc -> ValueEnv -> Type -> TCM Type
checkSkolems p what tyEnv ty = do
  m     <- getModuleIdent
  theta <- getTypeSubst
  let ty' = subst theta ty
      fs  = fsEnv $ subst theta tyEnv
  unless (all (`Set.member` fs) $ typeSkolems ty') $
           report $ errSkolemEscapingScope p m what ty'
  return ty'

-- Instantiation and Generalization:
-- We use negative offsets for fresh type variables.

fresh :: (Int -> a) -> TCM a
fresh f = f <$> getNextId

freshVar :: (Int -> a) -> TCM a
freshVar f = fresh $ \ n -> f (- n - 1)

freshTypeVar :: TCM Type
freshTypeVar = freshVar TypeVariable

freshConstrained :: [Type] -> TCM Type
freshConstrained = freshVar . TypeConstrained

freshSkolem :: TCM Type
freshSkolem = fresh TypeSkolem

inst :: TypeScheme -> TCM Type
inst (ForAll n ty) = do
  tys <- replicateM n freshTypeVar
  return $ expandAliasType tys ty

instExist :: ExistTypeScheme -> TCM Type
instExist (ForAllExist n n' ty) = do
  tys <- replicateM (n + n') freshTypeVar
  return $ expandAliasType tys ty

skol :: ExistTypeScheme -> TCM Type
skol (ForAllExist n n' ty) = do
  tys  <- replicateM n  freshTypeVar
  tys' <- replicateM n' freshSkolem
  return $ expandAliasType (tys ++ tys') ty

gen :: Set.Set Int -> Type -> TypeScheme
gen gvs ty = ForAll (length tvs)
                    (subst (foldr2 bindSubst idSubst tvs tvs') ty)
  where tvs = [tv | tv <- nub (typeVars ty), tv `Set.notMember` gvs]
        tvs' = map TypeVariable [0 ..]

-- Auxiliary Functions:
-- The functions 'constrType', 'varType', and 'funType' are used to retrieve
-- the type of constructors, pattern variables, and variables in expressions,
-- respectively, from the type environment. Because the syntactical correctness
-- has already been verified by the syntax checker, none of these functions
-- should fail.

-- Note that 'varType' can handle ambiguous identifiers and returns the first
-- available type. This function is used for looking up the type of an
-- identifier on the left hand side of a rule where it unambiguously refers
-- to the local definition.

constrType :: ModuleIdent -> QualIdent -> ValueEnv -> ExistTypeScheme
constrType m c tyEnv = case qualLookupValue c tyEnv of
  [DataConstructor  _ _ _ sigma] -> sigma
  [NewtypeConstructor _ _ sigma] -> sigma
  _ -> case qualLookupValue (qualQualify m c) tyEnv of
    [DataConstructor  _ _ _ sigma] -> sigma
    [NewtypeConstructor _ _ sigma] -> sigma
    _ -> internalError $ "TypeCheck.constrType " ++ show c

varArity :: Ident -> ValueEnv -> Int
varArity v tyEnv = case lookupValue v tyEnv of
  Value _ a _ : _ -> a
  _ -> internalError $ "TypeCheck.varArity " ++ show v

varType :: Ident -> ValueEnv -> TypeScheme
varType v tyEnv = case lookupValue v tyEnv of
  Value _ _ sigma : _ -> sigma
  _ -> internalError $ "TypeCheck.varType " ++ show v

sureVarType :: Ident -> ValueEnv -> Maybe TypeScheme
sureVarType v tyEnv = case lookupValue v tyEnv of
  Value _ _ sigma : _ -> Just sigma
  _ -> Nothing

funType :: ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
funType m f tyEnv = case qualLookupValue f tyEnv of
  [Value _ _ sigma] -> sigma
  [Label _ _ sigma] -> sigma
  _                 -> case qualLookupValue (qualQualify m f) tyEnv of
    [Value _ _ sigma] -> sigma
    [Label _ _ sigma] -> sigma
    _                 -> internalError $ "TypeCheck.funType " ++ show f
                          ++ ", more precisely " ++ show (unqualify f)

labelType :: ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
labelType m l tyEnv = case qualLookupValue l tyEnv of
  [Label _ _ sigma] -> sigma
  _ -> case qualLookupValue ql tyEnv of
    [Label _ _ sigma] -> sigma
    _ -> internalError $ "TypeCheck.labelType " ++ show ql
          ++ ", more precisely " ++ show l
  where ql = qualQualify m l

-- The function 'expandType' expands all type synonyms in a type
-- and also qualifies all type constructors with the name of the module
-- in which the type was defined.

expandPolyType :: TypeExpr -> TCM TypeScheme
expandPolyType ty = (polyType . normalize) <$> expandMonoType [] ty

expandMonoType :: [Ident] -> TypeExpr -> TCM Type
expandMonoType tvs ty = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  return $ expandMonoType' m tcEnv tvs ty

expandMonoType' :: ModuleIdent -> TCEnv -> [Ident] -> TypeExpr -> Type
expandMonoType' m tcEnv tvs ty = expandType m tcEnv (toType tvs ty)

expandMonoTypes :: ModuleIdent -> TCEnv -> [Ident] -> [TypeExpr] -> [Type]
expandMonoTypes m tcEnv tvs tys = map (expandType m tcEnv) (toTypes tvs tys)

expandType :: ModuleIdent -> TCEnv -> Type -> Type
expandType m tcEnv (TypeConstructor tc tys) = case qualLookupTC tc tcEnv of
  [DataType     tc' _  _] -> TypeConstructor tc' tys'
  [RenamingType tc' _  _] -> TypeConstructor tc' tys'
  [AliasType    _   _ ty] -> expandAliasType tys' ty
  _ -> case qualLookupTC (qualQualify m tc) tcEnv of
    [DataType     tc' _ _ ] -> TypeConstructor tc' tys'
    [RenamingType tc' _ _ ] -> TypeConstructor tc' tys'
    [AliasType    _   _ ty] -> expandAliasType tys' ty
    _ -> internalError $ "TypeCheck.expandType " ++ show tc
  where tys' = map (expandType m tcEnv) tys
expandType _ _     tv@(TypeVariable      _) = tv
expandType _ _     tc@(TypeConstrained _ _) = tc
expandType m tcEnv (TypeArrow      ty1 ty2) =
  TypeArrow (expandType m tcEnv ty1) (expandType m tcEnv ty2)
expandType _ _     ts@(TypeSkolem        _) = ts

-- The functions 'fvEnv' and 'fsEnv' compute the set of free type variables
-- and free skolems of a type environment, respectively. We ignore the types
-- of data constructors here because we know that they are closed.

fvEnv :: ValueEnv -> Set.Set Int
fvEnv tyEnv = Set.fromList
  [tv | ty <- localTypes tyEnv, tv <- typeVars ty, tv < 0]

fsEnv :: ValueEnv -> Set.Set Int
fsEnv = Set.unions . map (Set.fromList . typeSkolems) . localTypes

localTypes :: ValueEnv -> [Type]
localTypes tyEnv = [ty | (_, Value _ _ (ForAll _ ty)) <- localBindings tyEnv]

-- ---------------------------------------------------------------------------
-- Error functions
-- ---------------------------------------------------------------------------

errRecursiveTypes :: [Ident] -> Message
errRecursiveTypes []         = internalError
  "TypeCheck.recursiveTypes: empty list"
errRecursiveTypes [tc]       = posMessage tc $ hsep $ map text
  ["Recursive synonym type", idName tc]
errRecursiveTypes (tc : tcs) = posMessage tc $
  text "Recursive synonym types" <+> text (idName tc) <+> types empty tcs
  where
  types _    []         = empty
  types comm [tc1]      = comm <+> text "and" <+> text (idName tc1)
                          <+> parens (text $ showLine $ idPosition tc1)
  types _    (tc1:tcs1) = comma <+> text (idName tc1) <+>
                          parens (text $ showLine $ idPosition tc1)
                          <> types comma tcs1

errPolymorphicFreeVar :: Ident -> Message
errPolymorphicFreeVar v = posMessage v $ hsep $ map text
  ["Free variable", idName v, "has a polymorphic type"]

errTypeSigTooGeneral :: Position -> ModuleIdent -> Doc -> TypeExpr -> TypeScheme
                     -> Message
errTypeSigTooGeneral p m what ty sigma = posMessage p $ vcat
  [ text "Type signature too general", what
  , text "Inferred type:"  <+> ppTypeScheme m sigma
  , text "Type signature:" <+> ppTypeExpr 0 ty
  ]

errNonFunctionType :: Position -> String -> Doc -> ModuleIdent -> Type
                   -> Message
errNonFunctionType p what doc m ty = posMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be applied"
  ]

errNonBinaryOp :: Position -> String -> Doc -> ModuleIdent -> Type -> Message
errNonBinaryOp p what doc m ty = posMessage p $ vcat
  [ text "Type error in" <+> text what, doc
  , text "Type:" <+> ppType m ty
  , text "Cannot be used as binary operator"
  ]

errTypeMismatch :: Position -> String -> Doc -> ModuleIdent -> Type -> Type
                -> Doc -> Message
errTypeMismatch p what doc m ty1 ty2 reason = posMessage p $ vcat
  [ text "Type error in"  <+> text what, doc
  , text "Inferred type:" <+> ppType m ty2
  , text "Expected type:" <+> ppType m ty1
  , reason
  ]

errSkolemEscapingScope :: Position -> ModuleIdent -> Doc -> Type -> Message
errSkolemEscapingScope p m what ty = posMessage p $ vcat
  [ text "Existential type escapes out of its scope"
  , what, text "Type:" <+> ppType m ty
  ]

errRecursiveType :: ModuleIdent -> Int -> Type -> Doc
errRecursiveType m tv ty = errIncompatibleTypes m (TypeVariable tv) ty

errIncompatibleTypes :: ModuleIdent -> Type -> Type -> Doc
errIncompatibleTypes m ty1 ty2 = sep
  [ text "Types" <+> ppType m ty1
  , nest 2 $ text "and" <+> ppType m ty2
  , text "are incompatible"
  ]

errIncompatibleLabelTypes :: Position -> ModuleIdent -> Ident -> Type -> Type -> Message
errIncompatibleLabelTypes p m l ty1 ty2 = posMessage p $ sep
  [ text "Labeled types" <+> ppIdent l <+> text "::" <+> ppType m ty1
  , nest 10 $ text "and" <+> ppIdent l <+> text "::" <+> ppType m ty2
  , text "are incompatible"
  ]
