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
{-# LANGUAGE LambdaCase #-}
module Curry.Frontend.Checks.TypeSyntaxCheck (typeSyntaxCheck) where

import           Prelude hiding ((<>))
import           Control.Monad              ( filterM, unless, when )
import qualified Control.Monad.State as S   ( State, runState, gets, modify )
import           Data.List                  ( nub )
import           Data.List.NonEmpty         (NonEmpty(..))
import qualified Data.Map            as Map ( Map, insert, lookup )
import           Data.Maybe                 ( isNothing, mapMaybe )
import qualified Data.Set            as Set ( Set, fromList, isSubsetOf, size
                                            , toAscList, union )

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Curry.Frontend.Base.Expr (Expr (fv))
import Curry.Frontend.Base.Messages (Message, spanInfoMessage, internalError)
import Curry.Frontend.Base.TopEnv
import Curry.Frontend.Base.Utils (findMultiples, findDouble)

import           Curry.Frontend.Env.Class                 (ClassEnv)
import qualified Curry.Frontend.Env.Class           as CE (FunDep,toFunDep, toFunDepMap)
import           Curry.Frontend.Env.TypeConstructor       (TCEnv)
import           Curry.Frontend.Env.Type

-- TODO Use span info for err messages

-- TODO: If we decide to not allow repeating type variables in MPTC instance
--         heads, this can be checked here.
--       Could some functions which are almost identical in the type interface
--         check and the interface syntax check be unified?

-- In order to check type constructor applications, the compiler
-- maintains an environment containing all known type constructors and
-- type classes. The function 'typeSyntaxCheck' expects a type constructor
-- environment that is already initialized with the imported type constructors
-- and type classes. The type constructor environment is converted to a type
-- identifier environment, before all locally defined type constructors and
-- type classes are added to this environment and the declarations are checked
-- within this environment.

typeSyntaxCheck
  :: [KnownExtension] -> TCEnv -> ClassEnv -> Module a -> (Module a, [Message])
typeSyntaxCheck exts tcEnv clsEnv mdl@(Module _ _ _ m _ _ ds) =
  case findMultiples $ map getIdent tcds of
    [] -> if length dfps <= 1
            then runTSCM (checkModule mdl) state
            else (mdl, [errMultipleDefaultDeclarations dfps])
    tss -> (mdl, map errMultipleDeclarations tss)
  where
    tcds = filter isTypeOrClassDecl ds
    cds  = filter isClassDecl tcds
    dfps = mapMaybe (\case { DefaultDecl p _ -> Just p; _ -> Nothing }) ds
    tEnv = foldr (bindType m) (fmap toTypeKind tcEnv) tcds
    fdmap = foldr (bindClass m) (CE.toFunDepMap clsEnv) cds
    state = TSCState exts m tEnv fdmap 1 []

-- Type Syntax Check Monad
type TSCM = S.State TSCState

-- |Internal state of the Type Syntax Check
data TSCState = TSCState
  { extensions  :: [KnownExtension]
  , moduleIdent :: ModuleIdent
  , typeEnv     :: TypeEnv
  , simpClsEnv  :: SimpleClassEnv
  , nextId      :: Integer
  , errors      :: [Message]
  }

type SimpleClassEnv = Map.Map QualIdent [CE.FunDep]

runTSCM :: TSCM a -> TSCState -> (a, [Message])
runTSCM tscm s = let (a, s') = S.runState tscm s in (a, reverse $ errors s')

getExtensions :: TSCM [KnownExtension]
getExtensions = S.gets extensions

getModuleIdent :: TSCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getTypeEnv :: TSCM TypeEnv
getTypeEnv = S.gets typeEnv

getSimpleClassEnv :: TSCM SimpleClassEnv
getSimpleClassEnv = S.gets simpClsEnv

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
bindType m (ClassDecl _ _ _ cls _ _ ds) = bindTypeKind m cls (Class qcls ms)
  where
    qcls = qualifyWith m cls
    ms = concatMap methods ds
bindType _ _ = id

bindClass :: ModuleIdent -> Decl a -> SimpleClassEnv -> SimpleClassEnv
bindClass m (ClassDecl _ _ _ cls tvs fds _) = let qcls = qualifyWith m cls
                                                  fds' = map (CE.toFunDep tvs) fds
                                              in  Map.insert qcls fds'
bindClass _ _                               = id

-- When type declarations are checked, the compiler will allow anonymous
-- type variables on the left hand side of the declaration, but not on
-- the right hand side. Function and pattern declarations must be
-- traversed because they can contain local type signatures.

checkModule :: Module a -> TSCM (Module a)
checkModule (Module spi li ps m es is ds) = do
  ds' <- mapM checkDecl ds
  return $ Module spi li ps m es is ds'

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
checkDecl (TypeSig p vs qty)                  =
  TypeSig p vs <$> checkQualType qty
checkDecl (FunctionDecl a p f eqs)            = FunctionDecl a p f <$>
  mapM checkEquation eqs
checkDecl (PatternDecl p t rhs)               = PatternDecl p t <$> checkRhs rhs
checkDecl (DefaultDecl p tys)                 = DefaultDecl p <$>
  mapM (checkClosedType []) tys
checkDecl (ClassDecl p li cx cls clsvars funDeps ds) = do
  checkMPTCExtClass p cls clsvars
  checkFunDepExt p cls funDeps
  checkTypeVars "class declaration" clsvars
  cx' <- checkClosedContext True clsvars cx
  checkSimpleContext cx'
  funDeps' <- filterM (checkClosedFunDep clsvars) funDeps
  ds' <- mapM checkDecl ds
  return $ ClassDecl p li cx' cls clsvars funDeps' ds'
checkDecl (InstanceDecl p li cx qcls inst ds) = do
  checkMPTCExtInstance p qcls inst
  checkClass True qcls
  -- taken from Leif-Erik Krueger
  (cx', inst') <- checkQualTypes True cx inst
  mapM_ (checkInstanceType p) inst'
  InstanceDecl p li cx' qcls inst' <$> mapM checkDecl ds
checkDecl d                                   = return d

checkConstrDecl :: [Ident] -> ConstrDecl -> TSCM ConstrDecl
checkConstrDecl tvs (ConstrDecl p c tys) = do
  tys' <- mapM (checkClosedType tvs) tys
  return $ ConstrDecl p c tys'
checkConstrDecl tvs (ConOpDecl p ty1 op ty2) = do
  ty1' <- checkClosedType tvs ty1
  ty2' <- checkClosedType tvs ty2
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
checkSimpleConstraint c@(Constraint _ _ tys) =
  unless (all isVariableType tys) $ report $ errIllegalSimpleConstraint c

checkInstanceType :: SpanInfo -> InstanceType -> TSCM ()
checkInstanceType p inst = do
  tEnv <- getTypeEnv
  -- with FlexibleInstances, instance types must not contain anonymous
  -- variables or quantifiers, but can contain type synonyms or duplicate
  -- variables or may not be simple types.
  -- inspired by Leif-Erik Krueger
  exts <- getExtensions
  let flex = elem FlexibleInstances exts
  if any isAnonId (typeVariables inst) || containsForall inst
  then report $ errIllegalFlexibleInstanceType p inst
  else unless (flex || (isSimpleType inst &&
        not (isTypeSyn (typeConstr inst) tEnv) &&
        isNothing (findDouble $ fv inst))) $
          report $ errIllegalInstanceType p inst

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
checkEquation (Equation p a lhs rhs) = Equation p a lhs <$> checkRhs rhs

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

-- taken from Leif-Erik Krueger
checkQualType :: QualTypeExpr -> TSCM QualTypeExpr
checkQualType (QualTypeExpr spi cx ty) = do
  (cx', ty') <- checkQualTypes False cx [ty]
  return $ QualTypeExpr spi cx' (head ty')

-- taken from Leif-Erik Krueger
checkQualTypes :: Bool -> Context -> [TypeExpr] -> TSCM (Context, [TypeExpr])
checkQualTypes simplecx cx tys = do
  m <- getModuleIdent
  tys' <- mapM checkType tys
  fvs <- Set.toAscList <$> funDepCoverage m cx (Set.fromList $ fv tys)
  cx' <- checkClosedContext simplecx fvs cx
  return (cx', tys')

-- taken from Leif-Erik Krueger
checkClosedContext :: Bool -> [Ident] -> Context -> TSCM Context
checkClosedContext simplecx tvs = mapM (checkClosedConstraint simplecx tvs)

-- taken from Leif-Erik Krueger
checkClosedConstraint :: Bool -> [Ident] -> Constraint -> TSCM Constraint
checkClosedConstraint simplecx tvs c = do
  c'@(Constraint _ _ tys) <- checkConstraint simplecx c
  mapM_ (checkClosed tvs) tys
  return c'

checkConstraint :: Bool -> Constraint -> TSCM Constraint
checkConstraint simplecx c@(Constraint spi qcls tys) = do
  checkClass False qcls
  tys' <- mapM checkType tys
  -- taken from Leif-Erik Krueger
  flex <- elem FlexibleContexts <$> getExtensions
  case (any containsForall tys', simplecx) of
    (True , _    ) -> report $ errIllegalFlexibleConstraint c
    (False, True ) -> unless (flex || all isVariableType tys') $
                        report $ errIllegalSimpleConstraint c
    (False, False) -> unless (flex || all (isVariableType . rootType) tys') $
                        report $ errIllegalConstraint c
  return $ Constraint spi qcls tys'
  where
    rootType (ApplyType _ ty _) = rootType ty
    rootType (ParenType _ ty)   = rootType ty
    rootType ty                 = ty

checkClosedFunDep :: [Ident] -> FunDep -> TSCM Bool
checkClosedFunDep clsvars (FunDep _ ltvs rtvs) = do
  let unboundVars = filter (`notElem` clsvars) $ ltvs ++ rtvs
  mapM_ (report . errUnboundVariable) unboundVars
  return $ null unboundVars

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
      _   -> report $ errAmbiguousIdent qcls $ map origName tks

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
checkType (VariableType spi tv)
  | isAnonId tv = (VariableType spi . renameIdent tv) <$> newId
  | otherwise   = checkType $ ConstructorType spi (qualify tv)
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

checkMPTCExtClass :: SpanInfo -> Ident -> [Ident] -> TSCM ()
checkMPTCExtClass spi cls = checkMPTCExt (errMultiParamClassNoExt spi cls)

checkMPTCExtInstance :: SpanInfo -> QualIdent -> [InstanceType] -> TSCM ()
checkMPTCExtInstance spi qcls =
  checkMPTCExt (errMultiParamInstanceNoExt spi qcls)

checkMPTCExt :: ([paramType] -> Message) -> [paramType] -> TSCM ()
checkMPTCExt _       [_]    = ok
checkMPTCExt errFunc params = do
  exts <- getExtensions
  unless (MultiParamTypeClasses `elem` exts) $ report $ errFunc params

checkFunDepExt :: SpanInfo -> Ident -> [FunDep] -> TSCM ()
checkFunDepExt _   _   []      = ok
checkFunDepExt spi cls (_ : _) = do
  exts <- getExtensions
  unless (FunctionalDependencies `elem` exts) $ report $ errFunDepNoExt spi cls

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

getIdent :: Decl a -> Ident
getIdent (DataDecl     _ tc _ _ _)   = tc
getIdent (ExternalDataDecl _ tc _)   = tc
getIdent (NewtypeDecl _ tc _ _ _)    = tc
getIdent (TypeDecl _ tc _ _)         = tc
getIdent (ClassDecl _ _ _ cls _ _ _) = cls
getIdent _                           = internalError
  "Checks.TypeSyntaxCheck.getIdent: no type or class declaration"

isTypeSyn :: QualIdent -> TypeEnv -> Bool
isTypeSyn tc tEnv = case qualLookupTypeKind tc tEnv of
  [Alias _] -> True
  _ -> False

qualClassIdent :: ModuleIdent -> QualIdent -> TypeEnv -> Maybe QualIdent
qualClassIdent m qcls tEnv = case qualLookupTypeKind qcls tEnv of
  []              -> Nothing
  [Class qcls' _] -> Just qcls'
  [_]             -> Nothing
  _               ->
    case qualLookupTypeKind (qualQualify m qcls) tEnv of
      []                -> Nothing
      [Class qcls'  _]  -> Just qcls'
      [_]               -> Nothing
      _                 -> Nothing

funDepCoverage :: ModuleIdent -> Context -> Set.Set Ident -> TSCM (Set.Set Ident)
funDepCoverage m cx tvs = do
  simpleClsEnv <- getSimpleClassEnv
  tyEnv      <- getTypeEnv
  let tvs' = funDepCoverage' simpleClsEnv tyEnv tvs
  if Set.size tvs' == Set.size tvs
  then return tvs
  else funDepCoverage m cx tvs'
  where
   funDepCoverage' clsEnv tyEnv covVars =
    foldr (funDepCoverage'' clsEnv tyEnv) covVars cx

   funDepCoverage'' clsEnv tyEnv c@(Constraint _ cls _) covVars =
    case qualClassIdent m cls tyEnv of
      Nothing   -> covVars
      Just qcls ->
           let fds = lookupFunDeps qcls clsEnv
           in foldr (funDepCoverage''' c) covVars fds

   funDepCoverage''' (Constraint _ _ tys) (lixs,rixs) covVars =
    let lixs' = Set.toAscList lixs
        rixs' = Set.toAscList rixs
    in if Set.fromList (fv (filterIndices tys lixs')) `Set.isSubsetOf` tvs
       then covVars `Set.union` Set.fromList (fv (filterIndices tys rixs'))
       else covVars


lookupFunDeps :: QualIdent -> SimpleClassEnv -> [CE.FunDep]
lookupFunDeps qcls simpleClsEnv = case Map.lookup qcls simpleClsEnv of
  Nothing  -> []
  Just fds -> fds

filterIndices :: [a] -> [Int] -> [a]
filterIndices xs is = filterIndices' xs is 0
  where
    filterIndices' []     _      _             = []
    filterIndices' _      []     _             = []
    filterIndices' (y:ys) (j:js) k | j == k    = y : filterIndices' ys js (k+1)
                                   | otherwise = filterIndices' ys (j:js) (k+1)

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errMultipleDefaultDeclarations :: [SpanInfo] -> Message
errMultipleDefaultDeclarations spis = spanInfoMessage (head spis) $
  text "More than one default declaration:" $+$
    nest 2 (vcat $ map showPos spis)
  where showPos = text . showLine . getPosition

errMultipleDeclarations :: NonEmpty Ident -> Message
errMultipleDeclarations (i :| is) = spanInfoMessage i $
  text "Multiple declarations of" <+> text (escName i) <+> text "at:" $+$
    nest 2 (vcat $ map showPos (i:is))
  where i = head is
        showPos = text . showLine . getPosition

errUndefined :: String -> QualIdent -> Message
errUndefined what qident = spanInfoMessage qident $ hsep $ map text
  ["Undefined", what, qualName qident]

errUndefinedClass :: QualIdent -> Message
errUndefinedClass = errUndefined "class"

errUndefinedType :: QualIdent -> Message
errUndefinedType = errUndefined "type"

errAmbiguousIdent :: QualIdent -> [QualIdent] -> Message
errAmbiguousIdent qident qidents = spanInfoMessage qident $
  text "Ambiguous identifier" <+> text (escQualName qident) $+$
    text "It could refer to:" $+$ nest 2 (vcat (map (text . qualName) qidents))

errNonLinear :: Ident -> String -> Message
errNonLinear tv what = spanInfoMessage tv $ hsep $ map text
  [ "Type variable", idName tv, "occurs more than once in", what ]

errNoVariable :: Ident -> String -> Message
errNoVariable tv what = spanInfoMessage tv $ hsep $ map text
  ["Type constructor or type class identifier", idName tv, "used in", what]

errUnboundVariable :: Ident -> Message
errUnboundVariable tv = spanInfoMessage tv $ hsep $ map text
  [ "Unbound type variable", idName tv ]

errIllegalConstraint :: Constraint -> Message
errIllegalConstraint c@(Constraint _ qcls _) = spanInfoMessage qcls $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints must be of the form C u_1 ... u_n,"
  , text "where C is a type class and u_1, ..., u_n are type variables"
  , text "or type variables applied to types."
  , text "Use the FlexibleContexts extension if you want to allow this."
  ]

errIllegalSimpleConstraint :: Constraint -> Message
errIllegalSimpleConstraint c@(Constraint _ qcls _) = spanInfoMessage qcls $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints in class and instance declarations must be of"
  , text "the form C u_1 ... u_n, where C is a type class"
  , text "and u_1, ..., u_n are type variables."
  , text "Use the FlexibleContexts extension if you want to allow this."
  ]

-- taken from Leif-Erik Krueger
errIllegalFlexibleConstraint :: Constraint -> Message
errIllegalFlexibleConstraint c = spanInfoMessage c $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints must not contain type quantifiers."
  ]

-- taken from Leif-Erik Krueger
errIllegalInstanceType :: SpanInfo -> InstanceType -> Message
errIllegalInstanceType spi inst = spanInfoMessage spi $ vcat
  [ text "Illegal instance type" <+> ppInstanceType inst
  , text "Each instance type must be of the form (T u_1 ... u_n),"
  , text "where T is not a type synonym and u_1, ..., u_n are"
  , text "mutually distinct, non-anonymous type variables."
  , text "Use the FlexibleInstances extension if you want to allow this."
  ]

-- taken from Leif-Erik Krueger
errIllegalFlexibleInstanceType :: SpanInfo -> InstanceType -> Message
errIllegalFlexibleInstanceType spi inst = spanInfoMessage spi $ vcat
  [ text "Illegal instance type" <+> ppInstanceType inst
  , text "Each instance type must not contain anonymous"
  , text "type variables or quantified types."
  ]

errIllegalDataInstance :: QualIdent -> Message
errIllegalDataInstance qcls = spanInfoMessage qcls $ vcat
  [ text "Illegal instance of" <+> ppQIdent qcls
  , text "Instances of this class cannot be defined."
  , text "Instead, they are automatically derived if possible."
  ]

errMultiParamClassNoExt :: SpanInfo -> Ident -> [Ident] -> Message
errMultiParamClassNoExt spi cls clsvars =
  let arity = if null clsvars then "Nullary" else "Multi-parameter"
  in spanInfoMessage spi $ vcat
     [ text arity <+> text "type class declaration"
       <+> hsep (pPrint cls : map pPrint clsvars)
     , text "A type class must have exactly one type parameter."
     , text "Use the MultiParamTypeClasses extension to enable"
     , text "instance declarations with zero or multiple types."]

errMultiParamInstanceNoExt :: SpanInfo -> QualIdent -> [InstanceType] -> Message
errMultiParamInstanceNoExt spi qcls inst =
  let quantity = if null inst then "Zero" else "Multiple"
  in spanInfoMessage spi $ vcat
     [ text quantity <+> text "types in instance declaration"
       <+> hsep (pPrint qcls : map ppInstanceType inst)
     , text "An instance head must have exactly one type."
     , text "Use the MultiParamTypeClasses extension to enable"
     , text "instance declarations with zero or multiple types."]

errFunDepNoExt :: SpanInfo -> Ident -> Message
errFunDepNoExt spi cls = spanInfoMessage spi $ vcat $
  [ text "Class" <+> text (escName cls) <+> text "uses functional dependencies."
  , text "Use the FunctionalDependencies extension to enable"
  , text "class declarations with functional dependencies."
  ]
