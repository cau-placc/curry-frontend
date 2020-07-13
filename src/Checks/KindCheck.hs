{- |
    Module      :  $Header$
    Description :  Checks type kinds
    Copyright   :  (c) 2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After the type syntax has been checked und nullary type constructors and
   type variables have been disambiguated, the compiler infers kinds for all
   type constructors and type classes defined in the current module and
   performs kind checking on all type definitions and type signatures.
-}
{-# LANGUAGE CPP #-}
module Checks.KindCheck (kindCheck) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>))
#endif
import           Control.Monad            (when, foldM)
import           Control.Monad.Fix        (mfix)
import qualified Control.Monad.State as S (State, runState, gets, modify)
import           Data.List                (partition, nub)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.CurryKinds
import Base.Expr
import Base.Kinds
import Base.KindSubst
import Base.Messages (Message, posMessage, internalError)
import Base.SCC
import Base.TopEnv
import Base.Types
import Base.TypeExpansion

import Env.Class
import Env.TypeConstructor

-- In order to infer kinds for type constructors and type classes, the
-- compiler sorts the module's type and class declarations into minimal
-- recursive binding groups and then applies kind inference to each
-- declaration group. Besides inferring kinds for the type constructors
-- and type classes of a group, the compiler also checks that there are
-- no mutually recursive type synonym definitions and that the super class
-- hierarchy is acyclic. The former allows entering fully expanded type
-- synonyms into the type constructor environment.

kindCheck :: TCEnv -> ClassEnv -> Module a -> ((TCEnv, ClassEnv), [Message])
kindCheck tcEnv clsEnv (Module _ _ _ m _ _ ds) = runKCM check initState
  where
    check = do
      checkNonRecursiveTypes tds &&> checkAcyclicSuperClasses cds
      errs <- S.gets errors
      if null errs
         then checkDecls
         else return (tcEnv, clsEnv)
    checkDecls = do
      (tcEnv', clsEnv') <- kcDecls tcEnv clsEnv tcds
      mapM_ (kcDecl tcEnv') ods
      return (tcEnv', clsEnv')
    tds = filter isTypeDecl tcds
    cds = filter isClassDecl tcds
    (tcds, ods) = partition isTypeOrClassDecl ds
    initState  = KCState m idSubst 0 []

-- Kind Check Monad
type KCM = S.State KCState

-- |Internal state of the Kind Check
data KCState = KCState
  { moduleIdent :: ModuleIdent -- read only
  , kindSubst   :: KindSubst
  , nextId      :: Int         -- automatic counter
  , errors      :: [Message]
  }

(&&>) :: KCM () -> KCM () -> KCM ()
pre &&> suf = do
  errs <- pre >> S.gets errors
  when (null errs) suf

runKCM :: KCM a -> KCState -> (a, [Message])
runKCM kcm s = let (a, s') = S.runState kcm s in (a, reverse $ errors s')

getModuleIdent :: KCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getKindSubst :: KCM KindSubst
getKindSubst = S.gets kindSubst

modifyKindSubst :: (KindSubst -> KindSubst) -> KCM ()
modifyKindSubst f = S.modify $ \s -> s { kindSubst = f $ kindSubst s }

getNextId :: KCM Int
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

report :: Message -> KCM ()
report err = S.modify (\s -> s { errors = err : errors s })

ok :: KCM ()
ok = return ()

-- Minimal recursive declaration groups are computed using the sets of bound
-- and free type constructor and type class identifiers of the declarations.

bt :: Decl a -> [Ident]
bt (DataDecl     _ tc _ _ _) = [tc]
bt (ExternalDataDecl _ tc _) = [tc]
bt (NewtypeDecl  _ tc _ _ _) = [tc]
bt (TypeDecl       _ tc _ _) = [tc]
bt (ClassDecl _ _ _ cls _ _) = [cls]
bt _                         = []

ft :: ModuleIdent -> Decl a -> [Ident]
ft m d = fts m d []

class HasType a where
  fts :: ModuleIdent -> a -> [Ident] -> [Ident]

instance HasType a => HasType [a] where
  fts m = flip $ foldr $ fts m

instance HasType a => HasType (Maybe a) where
  fts m = maybe id $ fts m

instance HasType (Decl a) where
  fts _ (InfixDecl               _ _ _ _) = id
  fts m (DataDecl          _ _ _ cs clss) = fts m cs . fts m clss
  fts _ (ExternalDataDecl          _ _ _) = id
  fts m (NewtypeDecl       _ _ _ nc clss) = fts m nc . fts m clss
  fts m (TypeDecl               _ _ _ ty) = fts m ty
  fts m (TypeSig                  _ _ ty) = fts m ty
  fts m (FunctionDecl          _ _ _ eqs) = fts m eqs
  fts _ (ExternalDecl                _ _) = id
  fts m (PatternDecl             _ _ rhs) = fts m rhs
  fts _ (FreeDecl                    _ _) = id
  fts m (DefaultDecl               _ tys) = fts m tys
  fts m (ClassDecl         _ _ cx _ _ ds) = fts m cx . fts m ds
  fts m (InstanceDecl _ _ cx cls inst ds) =
    fts m cx . fts m cls . fts m inst . fts m ds

instance HasType ConstrDecl where
  fts m (ConstrDecl     _ _ tys) = fts m tys
  fts m (ConOpDecl  _ ty1 _ ty2) = fts m ty1 . fts m ty2
  fts m (RecordDecl      _ _ fs) = fts m fs

instance HasType FieldDecl where
  fts m (FieldDecl _ _ ty) = fts m ty

instance HasType NewConstrDecl where
  fts m (NewConstrDecl      _ _ ty) = fts m ty
  fts m (NewRecordDecl _ _ (_, ty)) = fts m ty

instance HasType Constraint where
  fts m (Constraint _ qcls _) = fts m qcls

instance HasType QualTypeExpr where
  fts m (QualTypeExpr _ cx ty) = fts m cx . fts m ty

instance HasType TypeExpr where
  fts m (ConstructorType     _ tc) = fts m tc
  fts m (ApplyType      _ ty1 ty2) = fts m ty1 . fts m ty2
  fts _ (VariableType         _ _) = id
  fts m (TupleType          _ tys) = (tupleId (length tys) :) . fts m tys
  fts m (ListType            _ ty) = (listId :) . fts m ty
  fts m (ArrowType      _ ty1 ty2) = (arrowId :) . fts m ty1 . fts m ty2
  fts m (ParenType           _ ty) = fts m ty
  fts m (ForallType        _ _ ty) = fts m ty

instance HasType (Equation a) where
  fts m (Equation _ _ rhs) = fts m rhs

instance HasType (Rhs a) where
  fts m (SimpleRhs  _ _ e  ds) = fts m e . fts m ds
  fts m (GuardedRhs _ _ es ds) = fts m es . fts m ds

instance HasType (CondExpr a) where
  fts m (CondExpr _ g e) = fts m g . fts m e

instance HasType (Expression a) where
  fts _ (Literal             _ _ _) = id
  fts _ (Variable            _ _ _) = id
  fts _ (Constructor         _ _ _) = id
  fts m (Paren                 _ e) = fts m e
  fts m (Typed              _ e ty) = fts m e . fts m ty
  fts m (Record           _ _ _ fs) = fts m fs
  fts m (RecordUpdate       _ e fs) = fts m e . fts m fs
  fts m (Tuple                _ es) = fts m es
  fts m (List               _ _ es) = fts m es
  fts m (ListCompr        _ e stms) = fts m e . fts m stms
  fts m (EnumFrom              _ e) = fts m e
  fts m (EnumFromThen      _ e1 e2) = fts m e1 . fts m e2
  fts m (EnumFromTo        _ e1 e2) = fts m e1 . fts m e2
  fts m (EnumFromThenTo _ e1 e2 e3) = fts m e1 . fts m e2 . fts m e3
  fts m (UnaryMinus            _ e) = fts m e
  fts m (Apply             _ e1 e2) = fts m e1 . fts m e2
  fts m (InfixApply      _ e1 _ e2) = fts m e1 . fts m e2
  fts m (LeftSection         _ e _) = fts m e
  fts m (RightSection        _ _ e) = fts m e
  fts m (Lambda              _ _ e) = fts m e
  fts m (Let              _ _ ds e) = fts m ds . fts m e
  fts m (Do             _ _ stms e) = fts m stms . fts m e
  fts m (IfThenElse     _ e1 e2 e3) = fts m e1 . fts m e2 . fts m e3
  fts m (Case           _ _ _ e as) = fts m e . fts m as

instance HasType (Statement a) where
  fts m (StmtExpr _    e) = fts m e
  fts m (StmtDecl _ _ ds) = fts m ds
  fts m (StmtBind _ _  e) = fts m e

instance HasType (Alt a) where
  fts m (Alt _ _ rhs) = fts m rhs

instance HasType a => HasType (Field a) where
  fts m (Field _ _ x) = fts m x

instance HasType QualIdent where
  fts m qident = maybe id (:) (localIdent m qident)

-- When types are entered into the type constructor environment, all type
-- synonyms occuring in the definitions are fully expanded (except for
-- record types) and all type constructors and type classes are qualified
-- with the name of the module in which they are defined. This is possible
-- because Curry does not allow (mutually) recursive type synonyms or
-- newtypes, which is checked in the function 'checkNonRecursiveTypes' below.

ft' :: ModuleIdent -> Decl a -> [Ident]
ft' _ (DataDecl     _ _ _ _ _) = []
ft' _ (ExternalDataDecl _ _ _) = []
ft' m (NewtypeDecl _ _ _ nc _) = fts m nc []
ft' m (TypeDecl      _ _ _ ty) = fts m ty []
ft' _ _                        = []

checkNonRecursiveTypes :: [Decl a] -> KCM ()
checkNonRecursiveTypes ds = do
  m <- getModuleIdent
  mapM_ checkTypeAndNewtypeDecls $ scc bt (ft' m) ds

checkTypeAndNewtypeDecls :: [Decl a] -> KCM ()
checkTypeAndNewtypeDecls [] =
  internalError "Checks.KindCheck.checkTypeAndNewtypeDecls: empty list"
checkTypeAndNewtypeDecls [DataDecl _ _ _ _ _] = ok
checkTypeAndNewtypeDecls [ExternalDataDecl _ _ _] = ok
checkTypeAndNewtypeDecls [d] | isTypeOrNewtypeDecl d = do
  m <- getModuleIdent
  let tc = typeConstructor d
  when (tc `elem` ft m d) $ report $ errRecursiveTypes [tc]
checkTypeAndNewtypeDecls (d:ds) | isTypeOrNewtypeDecl d =
  report $ errRecursiveTypes $
    typeConstructor d : [typeConstructor d' | d' <- ds, isTypeOrNewtypeDecl d']
checkTypeAndNewtypeDecls _ = internalError
  "Checks.KindCheck.checkTypeAndNewtypeDecls: no type or newtype declarations"

-- The function 'checkAcyclicSuperClasses' checks that the super class
-- hierarchy is acyclic.

fc :: ModuleIdent -> Context -> [Ident]
fc m = foldr fc' []
  where
    fc' (Constraint _ qcls _) = maybe id (:) (localIdent m qcls)

checkAcyclicSuperClasses :: [Decl a] -> KCM ()
checkAcyclicSuperClasses ds = do
  m <- getModuleIdent
  mapM_ checkClassDecl $ scc bt (\(ClassDecl _ _ cx _ _ _) -> fc m cx) ds

checkClassDecl :: [Decl a] -> KCM ()
checkClassDecl [] =
  internalError "Checks.KindCheck.checkClassDecl: empty list"
checkClassDecl [ClassDecl _ _ cx cls _ _] = do
  m <- getModuleIdent
  when (cls `elem` fc m cx) $ report $ errRecursiveClasses [cls]
checkClassDecl (ClassDecl _ _ _ cls _ _ : ds) =
  report $ errRecursiveClasses $ cls : [cls' | ClassDecl _ _ _ cls' _ _ <- ds]
checkClassDecl _ =
  internalError "Checks.KindCheck.checkClassDecl: no class declaration"

-- For each declaration group, the kind checker first enters new
-- assumptions into the type constructor environment. For a type
-- constructor with arity n, we enter kind k_1 -> ... -> k_n -> k,
-- where k_i are fresh kind variables and k is * for data and newtype
-- type constructors and a fresh kind variable for type synonym type
-- constructors. For a type class we enter kind k, where k is a fresh
-- kind variable. We also add a type class to the class environment.
-- Next, the kind checker checks the declarations of the group within
-- the extended environment, and finally the kind checker instantiates
-- all remaining free kind variables to *.

-- As noted above, type synonyms are fully expanded while types are
-- entered into the type constructor environment. Furthermore, we uses
-- original names for classes and super classes in the class environment.
-- Unfortunately, both of this requires either sorting type declarations
-- properly or using the final type constructor environment for the expansion
-- and original names. We have chosen the latter option here, which requires
-- recursive monadic bindings which are supported using the 'mfix' method
-- from the 'MonadFix' type class.

bindKind :: ModuleIdent -> TCEnv -> ClassEnv -> TCEnv -> Decl a -> KCM TCEnv
bindKind m tcEnv' clsEnv tcEnv (DataDecl _ tc tvs cs _) =
  bindTypeConstructor DataType tc tvs (Just KindStar) (map mkData cs) tcEnv
  where
    mkData (ConstrDecl _     c  tys) = mkData' c  tys
    mkData (ConOpDecl  _ ty1 op ty2) = mkData' op [ty1, ty2]
    mkData (RecordDecl _     c   fs) =
      let (labels, tys) = unzip [(l, ty) | FieldDecl _ ls ty <- fs, l <- ls]
      in  mkRec c labels tys
    mkData' c tys = DataConstr c tys'
      where qtc = qualifyWith m tc
            PredType _ ty = expandConstrType m tcEnv' clsEnv qtc tvs tys
            tys' = arrowArgs ty
    mkRec c ls tys =
      RecordConstr c ls tys'
      where qtc = qualifyWith m tc
            PredType _ ty = expandConstrType m tcEnv' clsEnv qtc tvs tys
            tys' = arrowArgs ty
bindKind _ _     _       tcEnv (ExternalDataDecl _ tc tvs) =
  bindTypeConstructor DataType tc tvs (Just KindStar) [] tcEnv
bindKind m tcEnv' _      tcEnv (NewtypeDecl _ tc tvs nc _) =
  bindTypeConstructor RenamingType tc tvs (Just KindStar) (mkData nc) tcEnv
  where
    mkData (NewConstrDecl _ c      ty) = DataConstr c [ty']
      where ty'  = expandMonoType m tcEnv' tvs ty
    mkData (NewRecordDecl _ c (l, ty)) = RecordConstr c [l] [ty']
      where ty'  = expandMonoType m tcEnv' tvs ty
bindKind m tcEnv' _      tcEnv (TypeDecl _ tc tvs ty) =
  bindTypeConstructor aliasType tc tvs Nothing ty' tcEnv
  where
    aliasType tc' k = AliasType tc' k $ length tvs
    ty' = expandMonoType m tcEnv' tvs ty
bindKind m tcEnv' clsEnv tcEnv (ClassDecl _ _ _ cls tv ds) =
  bindTypeClass cls (concatMap mkMethods ds) tcEnv
  where
    mkMethods (TypeSig _ fs qty) = map (mkMethod qty) fs
    mkMethods _                  = []
    mkMethod qty f = ClassMethod f (findArity f ds) $
                       expandMethodType m tcEnv' clsEnv (qualify cls) tv qty
    findArity _ []                                    = Nothing
    findArity f (FunctionDecl _ _ f' eqs:_) | f == f' =
      Just $ eqnArity $ head eqs
    findArity f (_:ds')                               = findArity f ds'
bindKind _ _      _      tcEnv _                          = return tcEnv

bindTypeConstructor :: (QualIdent -> Kind -> a -> TypeInfo) -> Ident
                    -> [Ident] -> Maybe Kind -> a -> TCEnv -> KCM TCEnv
bindTypeConstructor f tc tvs k x tcEnv = do
  m <- getModuleIdent
  k' <- maybe freshKindVar return k
  ks <- mapM (const freshKindVar) tvs
  let qtc = qualifyWith m tc
      ti = f qtc (foldr KindArrow k' ks) x
  return $ bindTypeInfo m tc ti tcEnv

bindTypeClass :: Ident -> [ClassMethod] -> TCEnv -> KCM TCEnv
bindTypeClass cls ms tcEnv = do
  m <- getModuleIdent
  k <- freshKindVar
  let qcls = qualifyWith m cls
      ti = TypeClass qcls k ms
  return $ bindTypeInfo m cls ti tcEnv

bindFreshKind :: TCEnv -> Ident -> KCM TCEnv
bindFreshKind tcEnv tv = do
  k <- freshKindVar
  return $ bindTypeVar tv k tcEnv

bindTypeVars :: Ident -> [Ident] -> TCEnv -> KCM (Kind, TCEnv)
bindTypeVars tc tvs tcEnv = do
  m <- getModuleIdent
  return $ foldl (\(KindArrow k1 k2, tcEnv') tv ->
                   (k2, bindTypeVar tv k1 tcEnv'))
                 (tcKind m (qualifyWith m tc) tcEnv, tcEnv)
                 tvs

bindTypeVar :: Ident -> Kind -> TCEnv -> TCEnv
bindTypeVar ident k = bindTopEnv ident (TypeVar k)

bindClass :: ModuleIdent -> TCEnv -> ClassEnv -> Decl a -> ClassEnv
bindClass m tcEnv clsEnv (ClassDecl _ _ cx cls _ ds) =
  bindClassInfo qcls (sclss, ms) clsEnv
  where qcls = qualifyWith m cls
        ms = map (\f -> (f, f `elem` fs)) $ concatMap methods ds
        fs = concatMap impls ds
        sclss = nub $ map (\(Constraint _ cls' _) -> getOrigName m cls' tcEnv) cx
bindClass _ _ clsEnv _ = clsEnv

instantiateWithDefaultKind :: TypeInfo -> TypeInfo
instantiateWithDefaultKind (DataType tc k cs) =
  DataType tc (defaultKind k) cs
instantiateWithDefaultKind (RenamingType tc k nc) =
  RenamingType tc (defaultKind k) nc
instantiateWithDefaultKind (AliasType tc k n ty) =
  AliasType tc (defaultKind k) n ty
instantiateWithDefaultKind (TypeClass cls k ms) =
  TypeClass cls (defaultKind k) ms
instantiateWithDefaultKind (TypeVar _) =
  internalError "Checks.KindCheck.instantiateWithDefaultKind: type variable"

kcDecls :: TCEnv -> ClassEnv -> [Decl a] -> KCM (TCEnv, ClassEnv)
kcDecls tcEnv clsEnv ds = do
  m <- getModuleIdent
  foldM (uncurry kcDeclGroup) (tcEnv, clsEnv) $ scc bt (ft m) ds

kcDeclGroup :: TCEnv -> ClassEnv -> [Decl a] -> KCM (TCEnv, ClassEnv)
kcDeclGroup tcEnv clsEnv ds = do
  m <- getModuleIdent
  (tcEnv', clsEnv') <- mfix (\ ~(tcEnv', clsEnv') ->
    flip (,) (foldl (bindClass m tcEnv') clsEnv ds) <$>
      foldM (bindKind m tcEnv' clsEnv') tcEnv ds)
  mapM_ (kcDecl tcEnv') ds
  theta <- getKindSubst
  return (fmap (instantiateWithDefaultKind . subst theta) tcEnv', clsEnv')

-- After adding new assumptions to the environment, kind inference is
-- applied to all declarations. The type environment may be extended
-- temporarily with bindings for type variables occurring in the left
-- hand side of type declarations and free type variables of type
-- signatures. While the kinds of the former are determined already by
-- the kinds of their type constructors and type classes, respectively,
-- fresh kind variables are added for the latter.

kcDecl :: TCEnv -> Decl a -> KCM ()
kcDecl _     (InfixDecl _ _ _ _) = ok
kcDecl tcEnv (DataDecl _ tc tvs cs _) = do
  (_, tcEnv') <- bindTypeVars tc tvs tcEnv
  mapM_ (kcConstrDecl tcEnv') cs
kcDecl _     (ExternalDataDecl _ _ _) = ok
kcDecl tcEnv (NewtypeDecl _ tc tvs nc _) = do
  (_, tcEnv') <- bindTypeVars tc tvs tcEnv
  kcNewConstrDecl tcEnv' nc
kcDecl tcEnv t@(TypeDecl p tc tvs ty) = do
  (k, tcEnv') <- bindTypeVars tc tvs tcEnv
  kcType tcEnv' p "type declaration" (pPrint t) k ty
kcDecl tcEnv (TypeSig p _ qty) = kcTypeSig tcEnv p qty
kcDecl tcEnv (FunctionDecl _ _ _ eqs) = mapM_ (kcEquation tcEnv) eqs
kcDecl _     (ExternalDecl _ _) = ok
kcDecl tcEnv (PatternDecl _ _ rhs) = kcRhs tcEnv rhs
kcDecl _     (FreeDecl _ _) = ok
kcDecl tcEnv (DefaultDecl p tys) = do
  tcEnv' <- foldM bindFreshKind tcEnv $ nub $ fv tys
  mapM_ (kcValueType tcEnv' p "default declaration" empty) tys
kcDecl tcEnv (ClassDecl p _ cx cls tv ds) = do
  m <- getModuleIdent
  let tcEnv' = bindTypeVar tv (clsKind m (qualifyWith m cls) tcEnv) tcEnv
  kcContext tcEnv' p cx
  mapM_ (kcDecl tcEnv') ds
kcDecl tcEnv (InstanceDecl p _ cx qcls inst ds) = do
  m <- getModuleIdent
  tcEnv' <- foldM bindFreshKind tcEnv $ fv inst
  kcContext tcEnv' p cx
  kcType tcEnv' p what doc (clsKind m qcls tcEnv) inst
  mapM_ (kcDecl tcEnv') ds
    where
      what = "instance declaration"
      doc = pPrint (InstanceDecl p WhitespaceLayout cx qcls inst [])

kcConstrDecl :: TCEnv -> ConstrDecl -> KCM ()
kcConstrDecl tcEnv d@(ConstrDecl p _ tys) = do
  mapM_ (kcValueType tcEnv p what doc) tys
    where
      what = "data constructor declaration"
      doc = pPrint d
kcConstrDecl tcEnv d@(ConOpDecl p ty1 _ ty2) = do
  kcValueType tcEnv p what doc ty1
  kcValueType tcEnv p what doc ty2
    where
      what = "data constructor declaration"
      doc = pPrint d
kcConstrDecl tcEnv (RecordDecl _ _ fs) = do
  mapM_ (kcFieldDecl tcEnv) fs

kcFieldDecl :: TCEnv -> FieldDecl -> KCM ()
kcFieldDecl tcEnv d@(FieldDecl p _ ty) =
  kcValueType tcEnv p "field declaration" (pPrint d) ty

kcNewConstrDecl :: TCEnv -> NewConstrDecl -> KCM ()
kcNewConstrDecl tcEnv d@(NewConstrDecl p _ ty) =
  kcValueType tcEnv p "newtype constructor declaration" (pPrint d) ty
kcNewConstrDecl tcEnv (NewRecordDecl p _ (l, ty)) =
  kcFieldDecl tcEnv (FieldDecl p [l] ty)

kcEquation :: TCEnv -> Equation a -> KCM ()
kcEquation tcEnv (Equation _ _ rhs) = kcRhs tcEnv rhs

kcRhs :: TCEnv -> Rhs a -> KCM ()
kcRhs tcEnv (SimpleRhs p _ e ds) = do
  kcExpr tcEnv p e
  mapM_ (kcDecl tcEnv) ds
kcRhs tcEnv (GuardedRhs _ _ es ds) = do
  mapM_ (kcCondExpr tcEnv) es
  mapM_ (kcDecl tcEnv) ds

kcCondExpr :: TCEnv -> CondExpr a -> KCM ()
kcCondExpr tcEnv (CondExpr p g e) = kcExpr tcEnv p g >> kcExpr tcEnv p e

kcExpr :: HasPosition p => TCEnv -> p -> Expression a -> KCM ()
kcExpr _     _ (Literal _ _ _) = ok
kcExpr _     _ (Variable _ _ _) = ok
kcExpr _     _ (Constructor _ _ _) = ok
kcExpr tcEnv p (Paren _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (Typed _ e qty) = do
  kcExpr tcEnv p e
  kcTypeSig tcEnv p qty
kcExpr tcEnv p (Record _ _ _ fs) = mapM_ (kcField tcEnv p) fs
kcExpr tcEnv p (RecordUpdate _ e fs) = do
  kcExpr tcEnv p e
  mapM_ (kcField tcEnv p) fs
kcExpr tcEnv p (Tuple _ es) = mapM_ (kcExpr tcEnv p) es
kcExpr tcEnv p (List _ _ es) = mapM_ (kcExpr tcEnv p) es
kcExpr tcEnv p (ListCompr _ e stms) = do
  kcExpr tcEnv p e
  mapM_ (kcStmt tcEnv p) stms
kcExpr tcEnv p (EnumFrom _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (EnumFromThen _ e1 e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (EnumFromTo _ e1 e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (EnumFromThenTo _ e1 e2 e3) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
  kcExpr tcEnv p e3
kcExpr tcEnv p (UnaryMinus _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (Apply _ e1 e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (InfixApply _ e1 _ e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (LeftSection _ e _) = kcExpr tcEnv p e
kcExpr tcEnv p (RightSection _ _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (Lambda _ _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (Let _ _ ds e) = do
  mapM_ (kcDecl tcEnv) ds
  kcExpr tcEnv p e
kcExpr tcEnv p (Do _ _ stms e) = do
  mapM_ (kcStmt tcEnv p) stms
  kcExpr tcEnv p e
kcExpr tcEnv p (IfThenElse _ e1 e2 e3) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
  kcExpr tcEnv p e3
kcExpr tcEnv p (Case _ _ _ e alts) = do
  kcExpr tcEnv p e
  mapM_ (kcAlt tcEnv) alts

kcStmt :: HasPosition p => TCEnv -> p -> Statement a -> KCM ()
kcStmt tcEnv p (StmtExpr _ e) = kcExpr tcEnv p e
kcStmt tcEnv _ (StmtDecl _ _ ds) = mapM_ (kcDecl tcEnv) ds
kcStmt tcEnv p (StmtBind _ _ e) = kcExpr tcEnv p e

kcAlt :: TCEnv -> Alt a -> KCM ()
kcAlt tcEnv (Alt _ _ rhs) = kcRhs tcEnv rhs

kcField :: HasPosition p => TCEnv -> p -> Field (Expression a) -> KCM ()
kcField tcEnv p (Field _ _ e) = kcExpr tcEnv p e

kcContext :: HasPosition p => TCEnv -> p -> Context -> KCM ()
kcContext tcEnv p = mapM_ (kcConstraint tcEnv p)

kcConstraint :: HasPosition p => TCEnv -> p -> Constraint -> KCM ()
kcConstraint tcEnv p sc@(Constraint _ qcls ty) = do
  m <- getModuleIdent
  kcType tcEnv p "class constraint" doc (clsKind m qcls tcEnv) ty
  where
    doc = pPrint sc

kcTypeSig :: HasPosition p => TCEnv -> p -> QualTypeExpr -> KCM ()
kcTypeSig tcEnv p (QualTypeExpr _ cx ty) = do
  tcEnv' <- foldM bindFreshKind tcEnv free
  kcContext tcEnv' p cx
  kcValueType tcEnv' p "type signature" doc ty
  where
    free = filter (null . flip lookupTypeInfo tcEnv) $ nub $ fv ty
    doc = pPrintPrec 0 ty

kcValueType :: HasPosition p => TCEnv -> p -> String -> Doc -> TypeExpr -> KCM ()
kcValueType tcEnv p what doc = kcType tcEnv p what doc KindStar

kcType :: HasPosition p => TCEnv -> p -> String -> Doc -> Kind -> TypeExpr -> KCM ()
kcType tcEnv p what doc k ty = do
  k' <- kcTypeExpr tcEnv p "type expression" doc' 0 ty
  unify p what (doc $-$ text "Type:" <+> doc') k k'
  where
    doc' = pPrintPrec 0 ty

kcTypeExpr :: HasPosition p => TCEnv -> p -> String -> Doc -> Int -> TypeExpr -> KCM Kind
kcTypeExpr tcEnv p _ _ n (ConstructorType _ tc) = do
  m <- getModuleIdent
  case qualLookupTypeInfo tc tcEnv of
    [AliasType _ _ n' _] -> case n >= n' of
      True -> return $ tcKind m tc tcEnv
      False -> do
        report $ errPartialAlias p tc n' n
        freshKindVar
    _ -> return $ tcKind m tc tcEnv
kcTypeExpr tcEnv p what doc n (ApplyType _ ty1 ty2) = do
  (alpha, beta) <- kcTypeExpr tcEnv p what doc (n + 1) ty1 >>=
    kcArrow p what (doc $-$ text "Type:" <+> pPrintPrec 0 ty1)
  kcTypeExpr tcEnv p what doc 0 ty2 >>=
    unify p what (doc $-$ text "Type:" <+> pPrintPrec 0 ty2) alpha
  return beta
kcTypeExpr tcEnv _ _ _ _ (VariableType _ tv) = return (varKind tv tcEnv)
kcTypeExpr tcEnv p what doc _ (TupleType _ tys) = do
  mapM_ (kcValueType tcEnv p what doc) tys
  return KindStar
kcTypeExpr tcEnv p what doc _ (ListType _ ty) = do
  kcValueType tcEnv p what doc ty
  return KindStar
kcTypeExpr tcEnv p what doc _ (ArrowType _ ty1 ty2) = do
  kcValueType tcEnv p what doc ty1
  kcValueType tcEnv p what doc ty2
  return KindStar
kcTypeExpr tcEnv p what doc n (ParenType _ ty) = kcTypeExpr tcEnv p what doc n ty
kcTypeExpr tcEnv p what doc n (ForallType _ vs ty) = do
  tcEnv' <- foldM bindFreshKind tcEnv vs
  kcTypeExpr tcEnv' p what doc n ty

kcArrow :: HasPosition p => p -> String -> Doc -> Kind -> KCM (Kind, Kind)
kcArrow p what doc k = do
  theta <- getKindSubst
  case subst theta k of
    KindStar -> do
      report $ errNonArrowKind p what doc KindStar
      (,) <$> freshKindVar <*> freshKindVar
    KindVariable kv -> do
      alpha <- freshKindVar
      beta <- freshKindVar
      modifyKindSubst $ bindVar kv $ KindArrow alpha beta
      return (alpha, beta)
    KindArrow k1 k2 -> return (k1, k2)

-- ---------------------------------------------------------------------------
-- Unification
-- ---------------------------------------------------------------------------

-- The unification uses Robinson's algorithm.
unify :: HasPosition p => p -> String -> Doc -> Kind -> Kind -> KCM ()
unify p what doc k1 k2 = do
  theta <- getKindSubst
  let k1' = subst theta k1
  let k2' = subst theta k2
  case unifyKinds k1' k2' of
    Nothing -> report $ errKindMismatch p what doc k1' k2'
    Just sigma -> modifyKindSubst (compose sigma)

unifyKinds :: Kind -> Kind -> Maybe KindSubst
unifyKinds KindStar KindStar = Just idSubst
unifyKinds (KindVariable kv1) (KindVariable kv2)
  | kv1 == kv2 = Just idSubst
  | otherwise  = Just (singleSubst kv1 (KindVariable kv2))
unifyKinds (KindVariable kv) k
  | kv `elem` kindVars k = Nothing
  | otherwise            = Just (singleSubst kv k)
unifyKinds k (KindVariable kv)
  | kv `elem` kindVars k = Nothing
  | otherwise            = Just (singleSubst kv k)
unifyKinds (KindArrow k11 k12) (KindArrow k21 k22) = do
  theta <- unifyKinds k11 k21
  theta' <- unifyKinds (subst theta k12) (subst theta k22)
  Just (compose theta' theta)
unifyKinds _ _ = Nothing

-- ---------------------------------------------------------------------------
-- Fresh variables
-- ---------------------------------------------------------------------------

fresh :: (Int -> a) -> KCM a
fresh f = f <$> getNextId

freshKindVar :: KCM Kind
freshKindVar = fresh KindVariable

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

typeConstructor :: Decl a -> Ident
typeConstructor (DataDecl     _ tc _ _ _) = tc
typeConstructor (ExternalDataDecl _ tc _) = tc
typeConstructor (NewtypeDecl  _ tc _ _ _) = tc
typeConstructor (TypeDecl     _ tc _ _  ) = tc
typeConstructor _                        =
  internalError "Checks.KindCheck.typeConstructor: no type declaration"

isTypeOrNewtypeDecl :: Decl a -> Bool
isTypeOrNewtypeDecl (NewtypeDecl _ _ _ _ _) = True
isTypeOrNewtypeDecl (TypeDecl      _ _ _ _) = True
isTypeOrNewtypeDecl _                       = False

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errRecursiveTypes :: [Ident] -> Message
errRecursiveTypes []       = internalError
  "KindCheck.errRecursiveTypes: empty list"
errRecursiveTypes [tc]     = posMessage tc $ hsep $ map text
  ["Recursive synonym or renaming type", idName tc]
errRecursiveTypes (tc:tcs) = posMessage tc $
  text "Mutually recursive synonym and/or renaming types" <+>
    text (idName tc) <> types empty tcs
  where
    types _   []         = empty
    types del [tc']      = del <> space <> text "and" <+> typePos tc'
    types _   (tc':tcs') = comma <+> typePos tc' <> types comma tcs'
    typePos tc' =
      text (idName tc') <+> parens (text $ showLine $ getPosition tc')

errRecursiveClasses :: [Ident] -> Message
errRecursiveClasses []         = internalError
  "KindCheck.errRecursiveClasses: empty list"
errRecursiveClasses [cls]      = posMessage cls $ hsep $ map text
  ["Recursive type class", idName cls]
errRecursiveClasses (cls:clss) = posMessage cls $
  text "Mutually recursive type classes" <+> text (idName cls) <>
    classes empty clss
  where
    classes _   []           = empty
    classes del [cls']       = del <> space <> text "and" <+> classPos cls'
    classes _   (cls':clss') = comma <+> classPos cls' <> classes comma clss'
    classPos cls' =
      text (idName cls') <+> parens (text $ showLine $ getPosition cls')

errNonArrowKind :: HasPosition p => p -> String -> Doc -> Kind -> Message
errNonArrowKind p what doc k = posMessage p $ vcat
  [ text "Kind error in" <+> text what, doc
  , text "Kind:" <+> ppKind k
  , text "Cannot be applied"
  ]

errPartialAlias :: HasPosition p => p -> QualIdent -> Int -> Int -> Message
errPartialAlias p tc arity argc = posMessage p $ hsep
  [ text "Type synonym", ppQIdent tc
  , text "requires at least"
  , int arity, text (plural arity "argument") <> comma
  , text "but is applied to only", int argc
  ]
  where
    plural n x = if n == 1 then x else x ++ "s"

errKindMismatch ::  HasPosition p => p -> String -> Doc -> Kind -> Kind -> Message
errKindMismatch p what doc k1 k2 = posMessage p $ vcat
  [ text "Kind error in"  <+> text what, doc
  , text "Inferred kind:" <+> ppKind k2
  , text "Expected kind:" <+> ppKind k1
  ]
