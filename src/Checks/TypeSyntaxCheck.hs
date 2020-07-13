{- |
    Module      :  $Header$
    Description :  Checks type syntax
    Copyright   :  (c) 2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After the source file has been parsed and all modules have been
   imported, the compiler first checks all type definitions and
   signatures. In particular, this module disambiguates nullary type
   constructors and type variables, which -- in contrast to Haskell -- is
   not possible on purely syntactic criteria. In addition it is checked
   that all type constructors and type variables occurring on the right
   hand side of a type declaration are actually defined and no identifier
   is defined more than once.
-}
{-# LANGUAGE CPP #-}
module Checks.TypeSyntaxCheck (typeSyntaxCheck) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>), pure)
#endif
import           Control.Monad            (unless, when)
import qualified Control.Monad.State as S (State, runState, gets, modify)
import           Data.List                (nub)
import qualified Data.Map as Map
import           Data.Maybe               (fromMaybe, isNothing)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.Expr (Expr (fv))
import Base.Messages (Message, posMessage, internalError)
import Base.TopEnv
import Base.Utils (findMultiples, findDouble)

import Env.TypeConstructor (TCEnv)
import Env.Type

-- TODO Use span info for err messages

-- In order to check type constructor applications, the compiler
-- maintains an environment containing all known type constructors and
-- type classes. The function 'typeSyntaxCheck' expects a type constructor
-- environment that is already initialized with the imported type constructors
-- and type classes. The type constructor environment is converted to a type
-- identifier environment, before all locally defined type constructors and
-- type classes are added to this environment and the declarations are checked
-- within this environment.

typeSyntaxCheck :: [KnownExtension] -> TCEnv -> Module a
                -> ((Module a, [KnownExtension]), [Message])
typeSyntaxCheck exts tcEnv mdl@(Module _ _ _ m _ _ ds) =
  case findMultiples $ map getIdent tcds of
    [] -> if length dfds <= 1
            then runTSCM (checkModule mdl) state
            else ((mdl, exts), [errMultipleDefaultDeclarations dfps])
    tss -> ((mdl, exts), map errMultipleDeclarations tss)
  where
    tcds = filter isTypeOrClassDecl ds
    dfds = filter isDefaultDecl ds
    dfps = map (\(DefaultDecl p _) -> spanInfo2Pos p) dfds
    tEnv = foldr (bindType m) (fmap toTypeKind tcEnv) tcds
    state = TSCState m tEnv exts Map.empty 1 []

-- Type Syntax Check Monad
type TSCM = S.State TSCState

-- |Internal state of the Type Syntax Check
data TSCState = TSCState
  { moduleIdent :: ModuleIdent
  , typeEnv     :: TypeEnv
  , extensions  :: [KnownExtension]
  , renameEnv   :: RenameEnv
  , nextId      :: Integer
  , errors      :: [Message]
  }

runTSCM :: TSCM a -> TSCState -> (a, [Message])
runTSCM tscm s = let (a, s') = S.runState tscm s in (a, reverse $ errors s')

getModuleIdent :: TSCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getTypeEnv :: TSCM TypeEnv
getTypeEnv = S.gets typeEnv

hasExtension :: KnownExtension -> TSCM Bool
hasExtension ext = S.gets (elem ext . extensions)

enableExtension :: KnownExtension -> TSCM ()
enableExtension e = S.modify $ \s -> s { extensions = e : extensions s }

getExtensions :: TSCM [KnownExtension]
getExtensions = S.gets extensions

getRenameEnv :: TSCM RenameEnv
getRenameEnv = S.gets renameEnv

modifyRenameEnv :: (RenameEnv -> RenameEnv) -> TSCM ()
modifyRenameEnv f = S.modify $ \s -> s { renameEnv = f $ renameEnv s }

withLocalEnv :: TSCM a -> TSCM a
withLocalEnv act = do
  oldEnv <- getRenameEnv
  res <- act
  modifyRenameEnv $ const oldEnv
  return res

resetEnv :: TSCM ()
resetEnv = modifyRenameEnv $ const Map.empty

newId :: TSCM Integer
newId = do
  curId <- S.gets nextId
  S.modify $ \s -> s { nextId = succ curId }
  return curId

report :: Message -> TSCM ()
report err = S.modify (\s -> s { errors = err : errors s })

ok :: TSCM ()
ok = return ()

bindType :: ModuleIdent -> Decl a -> TypeEnv -> TypeEnv
bindType m (DataDecl _ tc _ cs _) = bindTypeKind m tc (Data qtc ids)
  where
    qtc = qualifyWith m tc
    ids = map constrId cs ++ nub (concatMap recordLabels cs)
bindType m (ExternalDataDecl _ tc _) = bindTypeKind m tc (Data qtc [])
  where
    qtc = qualifyWith m tc
bindType m (NewtypeDecl _ tc _ nc _) = bindTypeKind m tc (Data qtc ids)
  where
    qtc = qualifyWith m tc
    ids = nconstrId nc : nrecordLabels nc
bindType m (TypeDecl _ tc _ _) = bindTypeKind m tc (Alias qtc)
  where
    qtc = qualifyWith m tc
bindType m (ClassDecl _ _ _ cls _ ds)  = bindTypeKind m cls (Class qcls ms)
  where
    qcls = qualifyWith m cls
    ms = concatMap methods ds
bindType _ _ = id

-- As preparation for the kind check, type variables within type declarations
-- have to be renamed since existentially quantified type variable may shadow
-- a universally quantified variable from the left hand side of a type
-- declaration.

-- TODO: This renaming may be used to support scoped type variables in future.

-- TODO: In the long run, this renaming may be merged with the syntax check
-- renaming and moved into a separate module.

type RenameEnv = Map.Map Ident Ident

class Rename a where
  rename :: a -> TSCM a

renameTypeSig :: (Expr a, Rename a) => a -> TSCM a
renameTypeSig x = withLocalEnv $ do
  env <- getRenameEnv
  bindVars (filter (`notElem` Map.keys env) $ fv x)
  rename x

renameReset :: Rename a => a -> TSCM a
renameReset x = withLocalEnv $ resetEnv >> rename x

instance Rename a => Rename [a] where
  rename = mapM rename

instance Rename (Decl a) where
  rename (InfixDecl p fix pr ops) = return $ InfixDecl p fix pr ops
  rename (DataDecl p tc tvs cs clss) = withLocalEnv $ do
    bindVars tvs
    DataDecl p tc <$> rename tvs <*> rename cs <*> pure clss
  rename (ExternalDataDecl p tc tvs) = withLocalEnv $ do
    bindVars tvs
    ExternalDataDecl p tc <$> rename tvs
  rename (NewtypeDecl p tc tvs nc clss) = withLocalEnv $ do
    bindVars tvs
    NewtypeDecl p tc <$> rename tvs <*> rename nc <*> pure clss
  rename (TypeDecl p tc tvs ty) = withLocalEnv $ do
    bindVars tvs
    TypeDecl p tc <$> rename tvs <*> rename ty
  rename (TypeSig p fs qty)                =
    TypeSig p fs <$> renameTypeSig qty
  rename (FunctionDecl p a f eqs)          =
    FunctionDecl p a f <$> renameReset eqs
  rename (PatternDecl p ts rhs)            =
    PatternDecl p ts <$> renameReset rhs
  rename (DefaultDecl p tys)               =
    DefaultDecl p <$> mapM renameTypeSig tys
  rename (ClassDecl p li cx cls tv ds)     = withLocalEnv $ do
    bindVar tv
    ClassDecl p li <$> rename cx <*> pure cls <*> rename tv <*> rename ds
  rename (InstanceDecl p li cx cls ty ds)  = withLocalEnv $ do
    bindVars (fv ty)
    flip (InstanceDecl p li) cls <$> rename cx <*> rename ty <*> renameReset ds
  rename decl                              = return decl

instance Rename ConstrDecl where
  rename (ConstrDecl p c tys)     = withLocalEnv $
    ConstrDecl p c <$> rename tys
  rename (ConOpDecl p ty1 op ty2) = withLocalEnv $
    ConOpDecl p <$> rename ty1 <*> pure op <*> rename ty2
  rename (RecordDecl p c fs)      = withLocalEnv $
    RecordDecl p c <$> rename fs

instance Rename FieldDecl where
  rename (FieldDecl p ls ty) = FieldDecl p ls <$> rename ty

instance Rename NewConstrDecl where
  rename (NewConstrDecl p c ty) = NewConstrDecl p c <$> rename ty
  rename (NewRecordDecl p c (l, ty)) = NewRecordDecl p c . (,) l <$> rename ty

instance Rename Constraint where
  rename (Constraint spi cls ty) = Constraint spi cls <$> rename ty

instance Rename QualTypeExpr where
  rename (QualTypeExpr spi cx ty) = QualTypeExpr spi <$> rename cx <*> rename ty

instance Rename TypeExpr where
  rename (ConstructorType spi tc) = return $ ConstructorType spi tc
  rename (ApplyType spi ty1 ty2) = ApplyType spi <$> rename ty1 <*> rename ty2
  rename (VariableType spi tv) = VariableType spi <$> rename tv
  rename (TupleType spi tys) = TupleType spi <$> rename tys
  rename (ListType spi ty) = ListType spi <$> rename ty
  rename (ArrowType spi ty1 ty2) = ArrowType spi <$> rename ty1 <*> rename ty2
  rename (ParenType spi ty) = ParenType spi <$> rename ty
  rename (ForallType spi vs ty) = do
    bindVars vs
    ForallType spi <$> mapM rename vs <*> rename ty

instance Rename (Equation a) where
  rename (Equation p lhs rhs) = Equation p lhs <$> rename rhs

instance Rename (Rhs a) where
  rename (SimpleRhs spi li e ds)   =
    SimpleRhs spi li <$> rename e <*> rename ds
  rename (GuardedRhs spi li es ds) =
    GuardedRhs spi li <$> rename es <*> rename ds

instance Rename (CondExpr a) where
  rename (CondExpr spi c e) = CondExpr spi <$> rename c <*> rename e

instance Rename (Expression a) where
  rename (Paren spi e)                 = Paren spi <$> rename e
  rename (Typed spi e qty)             = Typed spi <$> rename e
                                                   <*> renameTypeSig qty
  rename (Record spi a c fs)           = Record spi a c <$> rename fs
  rename (RecordUpdate spi e fs)       = RecordUpdate spi <$> rename e
                                                          <*> rename fs
  rename (Tuple spi es)                = Tuple spi <$> rename es
  rename (List spi a es)               = List spi a <$> rename es
  rename (ListCompr spi e stmts)       = ListCompr spi <$> rename e
                                                       <*> rename stmts
  rename (EnumFrom spi e)              = EnumFrom spi <$> rename e
  rename (EnumFromThen spi e1 e2)      = EnumFromThen spi <$> rename e1
                                                          <*> rename e2
  rename (EnumFromTo spi e1 e2)        = EnumFromTo spi <$> rename e1
                                                        <*> rename e2
  rename (EnumFromThenTo spi e1 e2 e3) = EnumFromThenTo spi <$> rename e1
                                                            <*> rename e2
                                                            <*> rename e3
  rename (UnaryMinus spi e)            = UnaryMinus spi <$> rename e
  rename (Apply spi e1 e2)             = Apply spi <$> rename e1 <*> rename e2
  rename (InfixApply spi e1 op e2)     = flip (InfixApply spi) op <$> rename e1
                                                                  <*> rename e2
  rename (LeftSection spi e op)        = flip (LeftSection spi) op <$> rename e
  rename (RightSection spi op e)       = RightSection spi op <$> rename e
  rename (Lambda spi ts e)             = Lambda spi ts <$> rename e
  rename (Let spi li ds e)             = Let spi li <$> rename ds <*> rename e
  rename (Do spi li stmts e)           = Do spi li <$> rename stmts <*> rename e
  rename (IfThenElse spi c e1 e2)      = IfThenElse spi <$> rename c
                                                        <*> rename e1
                                                        <*> rename e2
  rename (Case spi li ct e alts)       = Case spi li ct <$> rename e
                                                        <*> rename alts
  rename expr                          = return expr

instance Rename (Statement a) where
  rename (StmtExpr spi e)     = StmtExpr spi    <$> rename e
  rename (StmtDecl spi li ds) = StmtDecl spi li <$> rename ds
  rename (StmtBind spi t e)   = StmtBind spi t  <$> rename e

instance Rename (Alt a) where
  rename (Alt spi t rhs) = Alt spi t <$> rename rhs

instance Rename a => Rename (Field a) where
  rename (Field spi l x) = Field spi l <$> rename x

instance Rename Ident where
  rename tv | isAnonId tv = renameIdent tv <$> newId
            | otherwise   = setSpanInfo (getSpanInfo tv) .
                            fromMaybe tv <$> lookupVar tv

bindVar :: Ident -> TSCM ()
bindVar tv = do
  k <- newId
  modifyRenameEnv $ Map.insert tv (renameIdent tv k)

bindVars :: [Ident] -> TSCM ()
bindVars = mapM_ bindVar

lookupVar :: Ident -> TSCM (Maybe Ident)
lookupVar tv = Map.lookup tv <$> getRenameEnv

-- When type declarations are checked, the compiler will allow anonymous
-- type variables on the left hand side of the declaration, but not on
-- the right hand side. Function and pattern declarations must be
-- traversed because they can contain local type signatures.

checkModule :: Module a -> TSCM (Module a, [KnownExtension])
checkModule (Module spi li ps m es is ds) = do
  ds' <- mapM checkDecl ds
  ds'' <- rename ds'
  exts <- getExtensions
  return (Module spi li ps m es is ds'', exts)

checkDecl :: Decl a -> TSCM (Decl a)
checkDecl (DataDecl p tc tvs cs clss)         = do
  checkTypeLhs tvs
  cs' <- mapM (checkConstrDecl tvs) cs
  mapM_ (checkClass False) clss
  return $ DataDecl p tc tvs cs' clss
checkDecl (NewtypeDecl p tc tvs nc clss)      = do
  checkTypeLhs tvs
  nc' <- checkNewConstrDecl tvs nc
  mapM_ (checkClass False) clss
  return $ NewtypeDecl p tc tvs nc' clss
checkDecl (TypeDecl p tc tvs ty)              = do
  checkTypeLhs tvs
  ty' <- checkClosedType tvs ty
  return $ TypeDecl p tc tvs ty'
checkDecl (TypeSig p vs qty)                   =
  TypeSig p vs <$> checkQualType qty
checkDecl (FunctionDecl a p f eqs)            = FunctionDecl a p f <$>
  mapM checkEquation eqs
checkDecl (PatternDecl p t rhs)               = PatternDecl p t <$> checkRhs rhs
checkDecl (DefaultDecl p tys)                 = DefaultDecl p <$>
  mapM (checkClosedType []) tys
checkDecl (ClassDecl p li cx cls clsvar ds)   = do
  checkTypeVars "class declaration" [clsvar]
  cx' <- checkClosedContext [clsvar] cx
  checkSimpleContext cx'
  ds' <- mapM checkDecl ds
  mapM_ (checkClassMethod clsvar) ds'
  return $ ClassDecl p li cx' cls clsvar ds'
checkDecl (InstanceDecl p li cx qcls inst ds) = do
  checkClass True qcls
  QualTypeExpr _ cx' inst' <- checkQualType $ QualTypeExpr NoSpanInfo cx inst
  checkSimpleContext cx'
  checkInstanceType p inst'
  InstanceDecl p li cx' qcls inst' <$> mapM checkDecl ds
checkDecl d                                   = return d

checkConstrDecl :: [Ident] -> ConstrDecl -> TSCM ConstrDecl
checkConstrDecl tvs (ConstrDecl p c tys) = do
  tys' <- mapM (checkClosedType tvs) tys
  return $ ConstrDecl p c tys'
checkConstrDecl tvs (ConOpDecl p ty1 op ty2) = do
  tys' <- mapM (checkClosedType tvs) [ty1, ty2]
  let [ty1', ty2'] = tys'
  return $ ConOpDecl p ty1' op ty2'
checkConstrDecl tvs (RecordDecl p c fs) = do
  fs' <- mapM (checkFieldDecl tvs) fs
  return $ RecordDecl p c fs'

checkFieldDecl :: [Ident] -> FieldDecl -> TSCM FieldDecl
checkFieldDecl tvs (FieldDecl p ls ty) =
  FieldDecl p ls <$> checkClosedType tvs ty

checkNewConstrDecl :: [Ident] -> NewConstrDecl -> TSCM NewConstrDecl
checkNewConstrDecl tvs (NewConstrDecl p c ty) = do
  ty'  <- checkClosedType tvs ty
  return $ NewConstrDecl p c ty'
checkNewConstrDecl tvs (NewRecordDecl p c (l, ty)) = do
  ty'  <- checkClosedType tvs ty
  return $ NewRecordDecl p c (l, ty')

checkSimpleContext :: Context -> TSCM ()
checkSimpleContext = mapM_ checkSimpleConstraint

checkSimpleConstraint :: Constraint -> TSCM ()
checkSimpleConstraint c@(Constraint _ _ ty) =
  unless (isVariableType ty) $ report $ errIllegalSimpleConstraint c

-- Class method's type signatures have to obey a few additional restrictions.
-- The class variable must appear in the method's type and the method's
-- context must not contain any additional constraints for that class variable.

checkClassMethod :: Ident -> Decl a -> TSCM ()
checkClassMethod tv (TypeSig spi _ qty) = do
  unless (tv `elem` fv qty) $ report $ errAmbiguousType p tv
  let QualTypeExpr _ cx _ = qty
  when (tv `elem` fv cx) $ report $ errConstrainedClassVariable p tv
  where p = spanInfo2Pos spi
checkClassMethod _ _ = ok

checkInstanceType :: SpanInfo -> InstanceType -> TSCM ()
checkInstanceType p inst = do
  tEnv <- getTypeEnv
  unless (isSimpleType inst &&
    not (isTypeSyn (typeConstr inst) tEnv) &&
    not (any isAnonId $ typeVariables inst) &&
    isNothing (findDouble $ fv inst)) $
      report $ errIllegalInstanceType (spanInfo2Pos p) inst

checkTypeLhs :: [Ident] -> TSCM ()
checkTypeLhs = checkTypeVars "left hand side of type declaration"

-- |Checks a list of type variables for
-- * Anonymous type variables are allowed
-- * only type variables (no type constructors)
-- * linearity
checkTypeVars :: String -> [Ident] -> TSCM ()
checkTypeVars _    []         = ok
checkTypeVars what (tv : tvs) = do
  unless (isAnonId tv) $ do
    isTypeConstrOrClass <- not . null . lookupTypeKind tv <$> getTypeEnv
    when isTypeConstrOrClass $ report $ errNoVariable tv what
    when (tv `elem` tvs) $ report $ errNonLinear tv what
  checkTypeVars what tvs

-- Checking expressions is rather straight forward. The compiler must
-- only traverse the structure of expressions in order to find local
-- declaration groups.

checkEquation :: Equation a -> TSCM (Equation a)
checkEquation (Equation p lhs rhs) = Equation p lhs <$> checkRhs rhs

checkRhs :: Rhs a -> TSCM (Rhs a)
checkRhs (SimpleRhs spi li e ds)   =
  SimpleRhs spi li <$> checkExpr e <*> mapM checkDecl ds
checkRhs (GuardedRhs spi li es ds) =
  GuardedRhs spi li <$> mapM checkCondExpr es <*> mapM checkDecl ds

checkCondExpr :: CondExpr a -> TSCM (CondExpr a)
checkCondExpr (CondExpr spi g e) = CondExpr spi <$> checkExpr g <*> checkExpr e

checkExpr :: Expression a -> TSCM (Expression a)
checkExpr l@(Literal             _ _ _) = return l
checkExpr v@(Variable            _ _ _) = return v
checkExpr c@(Constructor         _ _ _) = return c
checkExpr (Paren                 spi e) = Paren spi <$> checkExpr e
checkExpr (Typed             spi e qty) = Typed spi <$> checkExpr e
                                                    <*> checkQualType qty
checkExpr (Record           spi a c fs) =
  Record spi a c <$> mapM checkFieldExpr fs
checkExpr (RecordUpdate       spi e fs) =
  RecordUpdate spi <$> checkExpr e <*> mapM checkFieldExpr fs
checkExpr (Tuple                spi es) = Tuple spi <$> mapM checkExpr es
checkExpr (List               spi a es) = List spi a <$> mapM checkExpr es
checkExpr (ListCompr          spi e qs) = ListCompr spi <$> checkExpr e
                                                        <*> mapM checkStmt qs
checkExpr (EnumFrom              spi e) = EnumFrom spi <$> checkExpr e
checkExpr (EnumFromThen      spi e1 e2) = EnumFromThen spi <$> checkExpr e1
                                                           <*> checkExpr e2
checkExpr (EnumFromTo        spi e1 e2) = EnumFromTo spi <$> checkExpr e1
                                                         <*> checkExpr e2
checkExpr (EnumFromThenTo spi e1 e2 e3) = EnumFromThenTo spi <$> checkExpr e1
                                                             <*> checkExpr e2
                                                             <*> checkExpr e3
checkExpr (UnaryMinus            spi e) = UnaryMinus spi <$> checkExpr e
checkExpr (Apply             spi e1 e2) = Apply spi <$> checkExpr e1
                                                    <*> checkExpr e2
checkExpr (InfixApply     spi e1 op e2) = InfixApply spi <$> checkExpr e1
                                                         <*> return op
                                                         <*> checkExpr e2
checkExpr (LeftSection spi e op)        = flip (LeftSection spi) op <$>
  checkExpr e
checkExpr (RightSection spi op e)       = RightSection spi op <$> checkExpr e
checkExpr (Lambda spi ts e)             = Lambda spi ts <$> checkExpr e
checkExpr (Let spi li ds e)             = Let spi li <$> mapM checkDecl ds
                                                     <*> checkExpr e
checkExpr (Do spi li sts e)             = Do spi li <$> mapM checkStmt sts
                                                    <*> checkExpr e
checkExpr (IfThenElse spi e1 e2 e3)     = IfThenElse spi <$> checkExpr e1
                                                         <*> checkExpr e2
                                                         <*> checkExpr e3
checkExpr (Case spi li ct e alts)       = Case spi li ct <$> checkExpr e
                                                         <*> mapM checkAlt alts
checkExpr expr                          = return expr

checkStmt :: Statement a -> TSCM (Statement a)
checkStmt (StmtExpr spi e)     = StmtExpr spi    <$> checkExpr e
checkStmt (StmtBind spi t e)   = StmtBind spi t  <$> checkExpr e
checkStmt (StmtDecl spi li ds) = StmtDecl spi li <$> mapM checkDecl ds

checkAlt :: Alt a -> TSCM (Alt a)
checkAlt (Alt spi t rhs) = Alt spi t <$> checkRhs rhs

checkFieldExpr :: Field (Expression a) -> TSCM (Field (Expression a))
checkFieldExpr (Field spi l e) = Field spi l <$> checkExpr e

-- The parser cannot distinguish unqualified nullary type constructors
-- and type variables. Therefore, if the compiler finds an unbound
-- identifier in a position where a type variable is admissible, it will
-- interpret the identifier as such.

checkQualType :: QualTypeExpr -> TSCM QualTypeExpr
checkQualType (QualTypeExpr spi cx ty) = do
  ty' <- checkType ty
  cx' <- checkClosedContext (fv ty') cx
  return $ QualTypeExpr spi cx' ty'

checkClosedContext :: [Ident] -> Context -> TSCM Context
checkClosedContext tvs cx = do
  cx' <- checkContext cx
  mapM_ (\(Constraint _ _ ty) -> checkClosed tvs ty) cx'
  return cx'

checkContext :: Context -> TSCM Context
checkContext = mapM checkConstraint

checkConstraint :: Constraint -> TSCM Constraint
checkConstraint c@(Constraint spi qcls ty) = do
  checkClass False qcls
  ty' <- checkType ty
  unless (isVariableType $ rootType ty') $ report $ errIllegalConstraint c
  return $ Constraint spi qcls ty'
  where
    rootType (ApplyType _ ty' _) = ty'
    rootType ty'                 = ty'

checkClass :: Bool -> QualIdent -> TSCM ()
checkClass isInstDecl qcls = do
  m <- getModuleIdent
  tEnv <- getTypeEnv
  case qualLookupTypeKind qcls tEnv of
    [] -> report $ errUndefinedClass qcls
    [Class c _]
      | c == qDataId -> when (isInstDecl && m /= preludeMIdent) $ report $
                          errIllegalDataInstance qcls
      | otherwise    -> ok
    [_] -> report $ errUndefinedClass qcls
    tks -> case qualLookupTypeKind (qualQualify m qcls) tEnv of
      [Class c _]
        | c == qDataId -> when (isInstDecl && m /= preludeMIdent) $ report $
                            errIllegalDataInstance qcls
        | otherwise    -> ok
      [_] -> report $ errUndefinedClass qcls
      _ -> report $ errAmbiguousIdent qcls $ map origName tks

checkClosedType :: [Ident] -> TypeExpr -> TSCM TypeExpr
checkClosedType tvs ty = do
  ty' <- checkType ty
  checkClosed tvs ty'
  return ty'

checkType :: TypeExpr -> TSCM TypeExpr
checkType c@(ConstructorType spi tc) = do
  m <- getModuleIdent
  tEnv <- getTypeEnv
  case qualLookupTypeKind tc tEnv of
    []
      | isQTupleId tc -> return c
      | not (isQualified tc) -> return $ VariableType spi $ unqualify tc
      | otherwise -> report (errUndefinedType tc) >> return c
    [Class _ _] -> report (errUndefinedType tc) >> return c
    [_] -> return c
    tks -> case qualLookupTypeKind (qualQualify m tc) tEnv of
      [Class _ _] -> report (errUndefinedType tc) >> return c
      [_] -> return c
      _ -> report (errAmbiguousIdent tc $ map origName tks) >> return c
checkType (ApplyType spi ty1 ty2) = ApplyType spi <$> checkType ty1
                                                  <*> checkType ty2
checkType v@(VariableType spi tv)
  | isAnonId tv = return v
  | otherwise   = checkType $ ConstructorType  spi (qualify tv)
checkType (TupleType     spi tys) = TupleType  spi    <$> mapM checkType tys
checkType (ListType       spi ty) = ListType   spi    <$> checkType ty
checkType (ArrowType spi ty1 ty2) = ArrowType  spi    <$> checkType ty1
                                                      <*> checkType ty2
checkType (ParenType      spi ty) = ParenType  spi    <$> checkType ty
checkType (ForallType  spi vs ty) = ForallType spi vs <$> checkType ty

checkClosed :: [Ident] -> TypeExpr -> TSCM ()
checkClosed _   (ConstructorType _ _) = ok
checkClosed tvs (ApplyType _ ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (VariableType   _ tv) =
  when (isAnonId tv || tv `notElem` tvs) $ report $ errUnboundVariable tv
checkClosed tvs (TupleType     _ tys) = mapM_ (checkClosed tvs) tys
checkClosed tvs (ListType       _ ty) = checkClosed tvs ty
checkClosed tvs (ArrowType _ ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (ParenType      _ ty) = checkClosed tvs ty
checkClosed tvs (ForallType  _ vs ty) = checkClosed (tvs ++ vs) ty

checkUsedExtension :: Position -> String -> KnownExtension -> TSCM ()
checkUsedExtension pos msg ext = do
  enabled <- hasExtension ext
  unless enabled $ do
    report $ errMissingLanguageExtension pos msg ext
    enableExtension ext

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

getIdent :: Decl a -> Ident
getIdent (DataDecl     _ tc _ _ _) = tc
getIdent (ExternalDataDecl _ tc _) = tc
getIdent (NewtypeDecl _ tc _ _ _)  = tc
getIdent (TypeDecl _ tc _ _)       = tc
getIdent (ClassDecl _ _ _ cls _ _) = cls
getIdent _                         = internalError
  "Checks.TypeSyntaxCheck.getIdent: no type or class declaration"

isTypeSyn :: QualIdent -> TypeEnv -> Bool
isTypeSyn tc tEnv = case qualLookupTypeKind tc tEnv of
  [Alias _] -> True
  _ -> False

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errMultipleDefaultDeclarations :: [Position] -> Message
errMultipleDefaultDeclarations ps = posMessage (head ps) $
  text "More than one default declaration:" $+$
    nest 2 (vcat $ map showPos ps)
  where showPos = text . showLine

errMultipleDeclarations :: [Ident] -> Message
errMultipleDeclarations is = posMessage i $
  text "Multiple declarations of" <+> text (escName i) <+> text "at:" $+$
    nest 2 (vcat $ map showPos is)
  where i = head is
        showPos = text . showLine . getPosition

errMissingLanguageExtension :: Position -> String -> KnownExtension -> Message
errMissingLanguageExtension p what ext = posMessage p $
  text what <+> text "are not supported in standard Curry." $+$
  nest 2 (text "Use flag -X" <+> text (show ext)
          <+> text "to enable this extension.")

errUndefined :: String -> QualIdent -> Message
errUndefined what qident = posMessage qident $ hsep $ map text
  ["Undefined", what, qualName qident]

errUndefinedClass :: QualIdent -> Message
errUndefinedClass = errUndefined "class"

errUndefinedType :: QualIdent -> Message
errUndefinedType = errUndefined "type"

errAmbiguousIdent :: QualIdent -> [QualIdent] -> Message
errAmbiguousIdent qident qidents = posMessage qident $
  text "Ambiguous identifier" <+> text (escQualName qident) $+$
    text "It could refer to:" $+$ nest 2 (vcat (map (text . qualName) qidents))

errAmbiguousType :: Position -> Ident -> Message
errAmbiguousType p ident = posMessage p $ hsep $ map text
  [ "Method type does not mention class variable", idName ident ]

errConstrainedClassVariable :: Position -> Ident -> Message
errConstrainedClassVariable p ident = posMessage p $ hsep $ map text
  [ "Method context must not constrain class variable", idName ident ]

errNonLinear :: Ident -> String -> Message
errNonLinear tv what = posMessage tv $ hsep $ map text
  [ "Type variable", idName tv, "occurs more than once in", what ]

errNoVariable :: Ident -> String -> Message
errNoVariable tv what = posMessage tv $ hsep $ map text
  ["Type constructor or type class identifier", idName tv, "used in", what]

errUnboundVariable :: Ident -> Message
errUnboundVariable tv = posMessage tv $ hsep $ map text
  [ "Unbound type variable", idName tv ]

errIllegalConstraint :: Constraint -> Message
errIllegalConstraint c@(Constraint _ qcls _) = posMessage qcls $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints must be of the form C u or C (u t1 ... tn),"
  , text "where C is a type class, u is a type variable and t1, ..., tn are types."
  ]

errIllegalSimpleConstraint :: Constraint -> Message
errIllegalSimpleConstraint c@(Constraint _ qcls _) = posMessage qcls $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints in class and instance declarations must be of"
  , text "the form C u, where C is a type class and u is a type variable."
  ]

errIllegalInstanceType :: Position -> InstanceType -> Message
errIllegalInstanceType p inst = posMessage p $ vcat
  [ text "Illegal instance type" <+> ppInstanceType inst
  , text "The instance type must be of the form (T u_1 ... u_n),"
  , text "where T is not a type synonym and u_1, ..., u_n are"
  , text "mutually distinct, non-anonymous type variables."
  ]

errIllegalDataInstance :: QualIdent -> Message
errIllegalDataInstance qcls = posMessage qcls $ vcat
  [ text "Illegal instance of" <+> ppQIdent qcls
  , text "Instances of this class cannot be defined."
  , text "Instead, they are automatically derived if possible."
  ]
