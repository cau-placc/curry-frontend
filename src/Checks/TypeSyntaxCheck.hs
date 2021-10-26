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

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>), pure)
#endif
import           Control.Monad            (unless, when)
import qualified Control.Monad.State as S (State, runState, gets, modify)
import           Data.List                (nub)
import           Data.Maybe               (isNothing)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.Expr (Expr (fv))
import Base.Messages (Message, spanInfoMessage, internalError)
import Base.TopEnv
import Base.Utils (findMultiples, findDouble)

import Env.TypeConstructor (TCEnv)
import Env.Type

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
  :: [KnownExtension] -> TCEnv -> Module a -> (Module a, [Message])
typeSyntaxCheck exts tcEnv mdl@(Module _ _ _ m _ _ ds) =
  case findMultiples $ map getIdent tcds of
    [] -> if length dfds <= 1
            then runTSCM (checkModule mdl) state
            else (mdl, [errMultipleDefaultDeclarations dfps])
    tss -> (mdl, map errMultipleDeclarations tss)
  where
    tcds = filter isTypeOrClassDecl ds
    dfds = filter isDefaultDecl ds
    dfps = map (\(DefaultDecl p _) -> p) dfds
    tEnv = foldr (bindType m) (fmap toTypeKind tcEnv) tcds
    state = TSCState exts m tEnv 1 []

-- Type Syntax Check Monad
type TSCM = S.State TSCState

-- |Internal state of the Type Syntax Check
data TSCState = TSCState
  { extensions  :: [KnownExtension]
  , moduleIdent :: ModuleIdent
  , typeEnv     :: TypeEnv
  , nextId      :: Integer
  , errors      :: [Message]
  }

runTSCM :: TSCM a -> TSCState -> (a, [Message])
runTSCM tscm s = let (a, s') = S.runState tscm s in (a, reverse $ errors s')

getExtensions :: TSCM [KnownExtension]
getExtensions = S.gets extensions

getModuleIdent :: TSCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getTypeEnv :: TSCM TypeEnv
getTypeEnv = S.gets typeEnv

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
bindType m (ClassDecl _ _ _ cls _ ds) = bindTypeKind m cls (Class qcls ms)
  where
    qcls = qualifyWith m cls
    ms = concatMap methods ds
bindType _ _ = id

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
checkDecl (TypeSig p vs qty)                   =
  TypeSig p vs <$> checkQualType qty
checkDecl (FunctionDecl a p f eqs)            = FunctionDecl a p f <$>
  mapM checkEquation eqs
checkDecl (PatternDecl p t rhs)               = PatternDecl p t <$> checkRhs rhs
checkDecl (DefaultDecl p tys)                 = DefaultDecl p <$>
  mapM (checkClosedType []) tys
checkDecl (ClassDecl p li cx cls clsvars ds)  = do
  checkMPTCExtClass p cls clsvars
  checkTypeVars "class declaration" clsvars
  cx' <- checkClosedContext clsvars cx
  checkSimpleContext cx'
  ds' <- mapM checkDecl ds
  mapM_ (checkClassMethod clsvars) ds'
  return $ ClassDecl p li cx' cls clsvars ds'
checkDecl (InstanceDecl p li cx qcls inst ds) = do
  checkMPTCExtInstance p qcls inst
  checkClass True qcls
  (cx', inst') <- checkQualTypes cx inst
  checkSimpleContext cx'
  mapM_ (checkInstanceType p) inst'
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
checkSimpleContext cx = do flex <- elem FlexibleContexts <$> getExtensions
                           unless flex $ mapM_ checkSimpleConstraint cx

checkSimpleConstraint :: Constraint -> TSCM ()
checkSimpleConstraint c@(Constraint _ _ tys) =
  unless (all isVariableType tys) $ report $ errIllegalSimpleConstraint c

-- Class method's type signatures have to obey a few additional restrictions.
-- The class variables must all appear in the method's type and the method's
-- context must not contain any additional constraints for these class
-- variables.

checkClassMethod :: [Ident] -> Decl a -> TSCM ()
checkClassMethod tvs (TypeSig spi _ qty@(QualTypeExpr _ cx _)) = do
  mapM_ (report . errAmbiguousType spi) (filter (`notElem` fv qty) tvs)
  mapM_ (report . errConstrainedClassVariables spi)
        (filter ((\vs -> not (null vs) && all (`elem` tvs) vs) . fv) cx)
checkClassMethod _ _ = ok

checkInstanceType :: SpanInfo -> InstanceType -> TSCM ()
checkInstanceType p inst = do
  flex <- elem FlexibleInstances <$> getExtensions
  tEnv <- getTypeEnv
  unless (not (any isAnonId $ typeVariables inst) &&
    (flex || isSimpleType inst &&
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
  (cx', ty') <- checkQualTypes cx [ty]
  return $ QualTypeExpr spi cx' (head ty')

checkQualTypes :: Context -> [TypeExpr] -> TSCM (Context, [TypeExpr])
checkQualTypes cx tys = do
  tys' <- mapM checkType tys
  cx'  <- checkClosedContext (fv tys') cx
  return (cx', tys')

checkClosedContext :: [Ident] -> Context -> TSCM Context
checkClosedContext tvs = mapM (checkClosedConstraint tvs)

checkClosedConstraint :: [Ident] -> Constraint -> TSCM Constraint
checkClosedConstraint tvs c = do
  c'@(Constraint _ _ tys) <- checkConstraint c
  mapM_ (checkClosed tvs) tys
  return c'

checkConstraint :: Constraint -> TSCM Constraint
checkConstraint c@(Constraint spi qcls tys) = do
  checkClass False qcls
  tys' <- mapM checkType tys
  flex <- elem FlexibleContexts <$> getExtensions
  unless (flex || all (isVariableType . rootType) tys') $
    report $ errIllegalConstraint c
  return $ Constraint spi qcls tys'
  where
    rootType (ApplyType _ ty _) = rootType ty
    rootType (ParenType _ ty)   = rootType ty
    rootType ty                 = ty

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

errMultipleDefaultDeclarations :: [SpanInfo] -> Message
errMultipleDefaultDeclarations spis = spanInfoMessage (head spis) $
  text "More than one default declaration:" $+$
    nest 2 (vcat $ map showPos spis)
  where showPos = text . showLine . getPosition

errMultipleDeclarations :: [Ident] -> Message
errMultipleDeclarations is = spanInfoMessage i $
  text "Multiple declarations of" <+> text (escName i) <+> text "at:" $+$
    nest 2 (vcat $ map showPos is)
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

errAmbiguousType :: SpanInfo -> Ident -> Message
errAmbiguousType spi ident = spanInfoMessage spi $ hsep $ map text
  [ "Method type does not mention class variable", idName ident ]

errConstrainedClassVariables :: SpanInfo -> Constraint -> Message
errConstrainedClassVariables spi c = spanInfoMessage spi $ vcat
  [ text "Constraint" <+> pPrint c
  , text "in method context constrains only class variables"
  ]

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
  , text "(Use the FlexibleContexts extension to"
  , text "loosen these restrictions on constraints.)"
  ]

errIllegalSimpleConstraint :: Constraint -> Message
errIllegalSimpleConstraint c@(Constraint _ qcls _) = spanInfoMessage qcls $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints in class and instance declarations must be of"
  , text "the form C u_1 ... u_n, where C is a type class"
  , text "and u_1, ..., u_n are type variables."
  , text "(Use the FlexibleContexts extension to"
  , text "loosen these restrictions on constraints.)"
  ]

errIllegalInstanceType :: SpanInfo -> InstanceType -> Message
errIllegalInstanceType spi inst = spanInfoMessage spi $ vcat
  [ text "Illegal instance type" <+> ppInstanceType inst
  , text "Each instance type must be of the form (T u_1 ... u_n),"
  , text "where T is not a type synonym and u_1, ..., u_n are"
  , text "mutually distinct, non-anonymous type variables."
  , text "(Use the FlexibleInstances extension to"
  , text "loosen these restrictions on instance types.)"
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
     , text "nullary and multi-parameter type classes."]

errMultiParamInstanceNoExt :: SpanInfo -> QualIdent -> [InstanceType] -> Message
errMultiParamInstanceNoExt spi qcls inst =
  let quantity = if null inst then "Zero" else "Multiple"
  in spanInfoMessage spi $ vcat
     [ text quantity <+> text "types in instance declaration"
       <+> hsep (pPrint qcls : map ppInstanceType inst)
     , text "An instance head must have exactly one type."
     , text "Use the MultiParamTypeClasses extension to enable"
     , text "instance declarations with zero or multiple types."]
