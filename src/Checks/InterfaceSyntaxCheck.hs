{- |
    Module      :  $Header$
    Description :  Checks interface declarations
    Copyright   :  (c) 2000 - 2007 Wolfgang Lux
                       2011 - 2015 Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   Similar to Curry source files, some post-processing has to be applied
   to parsed interface files. In particular, the compiler must
   disambiguate nullary type constructors and type variables. In
   addition, the compiler also checks that all type constructor
   applications are saturated. Since interface files are closed -- i.e.,
   they include declarations of all entities which are defined in other
   modules -- the compiler can perform this check without reference to
   the global environments.
-}
{-# LANGUAGE CPP #-}
module Checks.InterfaceSyntaxCheck (intfSyntaxCheck) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import           Control.Monad            (liftM, liftM2, when)
import qualified Control.Monad.State as S
import           Data.List                (nub, partition)

import Base.Expr
import Base.Messages (Message, spanInfoMessage, internalError)
import Base.TopEnv
import Base.Utils    (findMultiples)

import Env.TypeConstructor
import Env.Type

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty ()

data ISCState = ISCState
  { typeEnv :: TypeEnv
  , errors  :: [Message]
  }

type ISC = S.State ISCState

getTypeEnv :: ISC TypeEnv
getTypeEnv = S.gets typeEnv

-- |Report a syntax error
report :: Message -> ISC ()
report msg = S.modify $ \ s -> s { errors = msg : errors s }

intfSyntaxCheck :: Interface -> (Interface, [Message])
intfSyntaxCheck (Interface n is ds) = (Interface n is ds', reverse $ errors s')
  where (ds', s') = S.runState (mapM checkIDecl ds) (ISCState env [])
        env = foldr bindType (fmap toTypeKind initTCEnv) ds

-- The compiler requires information about the arity of each defined type
-- constructor as well as information whether the type constructor
-- denotes an algebraic data type, a renaming type, or a type synonym.
-- The latter must not occur in type expressions in interfaces.

bindType :: IDecl -> TypeEnv -> TypeEnv
bindType (IInfixDecl           _ _ _ _) = id
bindType (HidingDataDecl      _ tc _ _) = qualBindTopEnv tc (Data tc [])
bindType (IDataDecl      _ tc _ _ cs _) = qualBindTopEnv tc $
  Data tc (map constrId cs)
bindType (INewtypeDecl   _ tc _ _ nc _) = qualBindTopEnv tc $
  Data tc [nconstrId nc]
bindType (ITypeDecl         _ tc _ _ _) = qualBindTopEnv tc (Alias tc)
bindType (IFunctionDecl      _ _ _ _ _) = id
bindType (HidingClassDecl  _ _ cls _ _) = qualBindTopEnv cls $ Class cls []
bindType (IClassDecl _ _ cls _ _ ms hs) = qualBindTopEnv cls $
  Class cls (filter (`notElem` hs) (map imethod ms))
bindType (IInstanceDecl    _ _ _ _ _ _) = id

-- The checks applied to the interface are similar to those performed
-- during syntax checking of type expressions.

checkIDecl :: IDecl -> ISC IDecl
checkIDecl (IInfixDecl  p fix pr op) = return (IInfixDecl p fix pr op)
checkIDecl (HidingDataDecl p tc k tvs) = do
  checkTypeLhs tvs
  return (HidingDataDecl p tc k tvs)
checkIDecl (IDataDecl p tc k tvs cs hs) = do
  checkTypeLhs tvs
  checkHiddenType tc (cons ++ labels) hs
  cs' <- mapM (checkConstrDecl tvs) cs
  return $ IDataDecl p tc k tvs cs' hs
  where cons   = map constrId cs
        labels = nub $ concatMap recordLabels cs
checkIDecl (INewtypeDecl p tc k tvs nc hs) = do
  checkTypeLhs tvs
  checkHiddenType tc (con : labels) hs
  nc' <- checkNewConstrDecl tvs nc
  return $ INewtypeDecl p tc k tvs nc' hs
  where con    = nconstrId nc
        labels = nrecordLabels nc
checkIDecl (ITypeDecl p tc k tvs ty) = do
  checkTypeLhs tvs
  liftM (ITypeDecl p tc k tvs) (checkClosedType tvs ty)
checkIDecl (IFunctionDecl p f cm n qty) =
  liftM (IFunctionDecl p f cm n) (checkQualType qty)
checkIDecl (HidingClassDecl p cx qcls k clsvars) = do
  checkTypeVars "hiding class declaration" clsvars
  cx' <- checkClosedContext clsvars cx
  return $ HidingClassDecl p cx' qcls k clsvars
checkIDecl (IClassDecl p cx qcls k clsvars ms hs) = do
  checkTypeVars "class declaration" clsvars
  cx' <- checkClosedContext clsvars cx
  ms' <- mapM (checkIMethodDecl clsvars) ms
  checkHidden (errNoElement "method" "class") qcls (map imethod ms') hs
  return $ IClassDecl p cx' qcls k clsvars ms' hs
checkIDecl (IInstanceDecl p cx qcls inst is m) = do
  checkClass qcls
  (cx', inst') <- checkQualTypes cx inst
  mapM_ checkInstanceType inst'
  mapM_ (report . errMultipleImplementation . head) $ findMultiples $ map fst is
  return $ IInstanceDecl p cx' qcls inst' is m

checkHiddenType :: QualIdent -> [Ident] -> [Ident] -> ISC ()
checkHiddenType = checkHidden $ errNoElement "constructor or label" "type"

checkHidden :: (QualIdent -> Ident -> Message) -> QualIdent -> [Ident]
            -> [Ident] -> ISC ()
checkHidden err tc csls hs =
  mapM_ (report . err tc) $ nub $ filter (`notElem` csls) hs

checkTypeLhs :: [Ident] -> ISC ()
checkTypeLhs = checkTypeVars "left hand side of type declaration"

checkTypeVars :: String -> [Ident] -> ISC ()
checkTypeVars what tvs = do
  tyEnv <- getTypeEnv
  let (tcs, tvs') = partition isTypeConstrOrClass tvs
      isTypeConstrOrClass tv = not (null (lookupTypeKind tv tyEnv))
  mapM_ (report . flip errNoVariable what)       (nub tcs)
  mapM_ (report . flip errNonLinear what . head) (findMultiples tvs')

checkConstrDecl :: [Ident] -> ConstrDecl -> ISC ConstrDecl
checkConstrDecl tvs (ConstrDecl p c tys) = do
  liftM (ConstrDecl p c) (mapM (checkClosedType tvs) tys)
checkConstrDecl tvs (ConOpDecl p ty1 op ty2) = do
  liftM2 (\t1 t2 -> ConOpDecl p t1 op t2)
         (checkClosedType tvs ty1)
         (checkClosedType tvs ty2)
checkConstrDecl tvs (RecordDecl p c fs) = do
  liftM (RecordDecl p c) (mapM (checkFieldDecl tvs) fs)

checkFieldDecl :: [Ident] -> FieldDecl -> ISC FieldDecl
checkFieldDecl tvs (FieldDecl p ls ty) =
  liftM (FieldDecl p ls) (checkClosedType tvs ty)

checkNewConstrDecl :: [Ident] -> NewConstrDecl -> ISC NewConstrDecl
checkNewConstrDecl tvs (NewConstrDecl p c ty) =
  liftM (NewConstrDecl p c) (checkClosedType tvs ty)
checkNewConstrDecl tvs (NewRecordDecl p c (l, ty)) = do
  ty' <- checkClosedType tvs ty
  return $ NewRecordDecl p c (l, ty')

checkIMethodDecl :: [Ident] -> IMethodDecl -> ISC IMethodDecl
checkIMethodDecl tvs (IMethodDecl p f a qty) = do
  qty'@(QualTypeExpr _ cx _) <- checkQualType qty
  mapM_ (report . errAmbiguousType f) (filter (`notElem` fv qty') tvs)
  mapM_ (report . errConstrainedClassVariables f)
        (filter ((\vs -> not (null vs) && all (`elem` tvs) vs) . fv) cx)
  return $ IMethodDecl p f a qty'

checkInstanceType :: InstanceType -> ISC ()
checkInstanceType inst =
  when (any isAnonId (typeVars inst) || containsForall inst) $
    report $ errIllegalInstanceType inst

checkQualType :: QualTypeExpr -> ISC QualTypeExpr
checkQualType (QualTypeExpr spi cx ty) = do
  (cx', ty') <- checkQualTypes cx [ty]
  return $ QualTypeExpr spi cx' (head ty')

checkQualTypes :: Context -> [TypeExpr] -> ISC (Context, [TypeExpr])
checkQualTypes cx tys = do
  tys' <- mapM checkType tys
  cx'  <- checkClosedContext (fv tys') cx
  return (cx', tys')

checkClosedContext :: [Ident] -> Context -> ISC Context
checkClosedContext tvs = mapM (checkClosedConstraint tvs)

checkClosedConstraint :: [Ident] -> Constraint -> ISC Constraint
checkClosedConstraint tvs c = do
  c'@(Constraint _ _ tys) <- checkConstraint c
  mapM_ (checkClosed tvs) tys
  return c'

checkConstraint :: Constraint -> ISC Constraint
checkConstraint c@(Constraint spi qcls tys) = do
  checkClass qcls
  when (any containsForall tys) $ report $ errIllegalConstraint c
  Constraint spi qcls `liftM` mapM checkType tys

checkClass :: QualIdent -> ISC ()
checkClass qcls = do
  tEnv <- getTypeEnv
  case qualLookupTypeKind qcls tEnv of
    []          -> report $ errUndefinedClass qcls
    [Class _ _] -> return ()
    [_]         -> report $ errUndefinedClass qcls
    _           -> internalError $ "Checks.InterfaceSyntaxCheck.checkClass: " ++
                                     "ambiguous identifier " ++ show qcls

checkClosedType :: [Ident] -> TypeExpr -> ISC TypeExpr
checkClosedType tvs ty = do
  ty' <- checkType ty
  checkClosed tvs ty'
  return ty'

checkType :: TypeExpr -> ISC TypeExpr
checkType (ConstructorType spi tc) = checkTypeConstructor spi tc
checkType (ApplyType  spi ty1 ty2) =
  liftM2 (ApplyType spi) (checkType ty1) (checkType ty2)
checkType (VariableType    spi tv) =
  checkType $ ConstructorType spi (qualify tv)
checkType (TupleType      spi tys) = liftM (TupleType spi) (mapM checkType tys)
checkType (ListType        spi ty) = liftM (ListType spi) (checkType ty)
checkType (ArrowType  spi ty1 ty2) =
  liftM2 (ArrowType spi) (checkType ty1) (checkType ty2)
checkType (ParenType      spi  ty) = liftM (ParenType spi) (checkType ty)
checkType (ForallType   spi vs ty) = liftM (ForallType spi vs) (checkType ty)

checkClosed :: [Ident] -> TypeExpr -> ISC ()
checkClosed _   (ConstructorType _ _) = return ()
checkClosed tvs (ApplyType _ ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (VariableType   _ tv) =
  when (isAnonId tv || tv `notElem` tvs) $ report $ errUnboundVariable tv
checkClosed tvs (TupleType     _ tys) = mapM_ (checkClosed tvs) tys
checkClosed tvs (ListType       _ ty) = checkClosed tvs ty
checkClosed tvs (ArrowType _ ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (ParenType      _ ty) = checkClosed tvs ty
checkClosed tvs (ForallType  _ vs ty) = checkClosed (tvs ++ vs) ty

checkTypeConstructor :: SpanInfo -> QualIdent -> ISC TypeExpr
checkTypeConstructor spi tc = do
  tyEnv <- getTypeEnv
  case qualLookupTypeKind tc tyEnv of
    [] | isQTupleId tc        -> return $ ConstructorType spi tc
       | not (isQualified tc) -> return $ VariableType spi $ unqualify tc
       | otherwise            -> do
          report $ errUndefinedType tc
          return $ ConstructorType spi tc
    [Data _ _] -> return $ ConstructorType spi tc
    [Alias  _] -> do
                  report $ errBadTypeSynonym tc
                  return $ ConstructorType spi tc
    _          ->
      internalError "Checks.InterfaceSyntaxCheck.checkTypeConstructor"

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

typeVars :: TypeExpr -> [Ident]
typeVars (ConstructorType      _ _) = []
typeVars (ApplyType      _ ty1 ty2) = typeVars ty1 ++ typeVars ty2
typeVars (VariableType        _ tv) = [tv]
typeVars (TupleType          _ tys) = concatMap typeVars tys
typeVars (ListType            _ ty) = typeVars ty
typeVars (ArrowType      _ ty1 ty2) = typeVars ty1 ++ typeVars ty2
typeVars (ParenType           _ ty) = typeVars ty
typeVars (ForallType       _ vs ty) = vs ++ typeVars ty

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errUndefined :: String -> QualIdent -> Message
errUndefined what qident = spanInfoMessage qident $ hsep $ map text
  ["Undefined", what, qualName qident]

errUndefinedClass :: QualIdent -> Message
errUndefinedClass = errUndefined "class"

errUndefinedType :: QualIdent -> Message
errUndefinedType = errUndefined "type"

errMultipleImplementation :: Ident -> Message
errMultipleImplementation f = spanInfoMessage f $ hsep $ map text
  ["Arity information for method", idName f, "occurs more than once"]

errAmbiguousType :: HasSpanInfo s => s -> Ident -> Message
errAmbiguousType p ident = spanInfoMessage p $ hsep $ map text
  [ "Method type does not mention class variable", idName ident ]

errConstrainedClassVariables :: HasSpanInfo s => s -> Constraint -> Message
errConstrainedClassVariables p c = spanInfoMessage p $ vcat
  [ text "Constraint" <+> pPrint c
  , text "in method context constrains only class variables."
  ]

errNonLinear :: Ident -> String -> Message
errNonLinear tv what = spanInfoMessage tv $ hsep $ map text
  [ "Type variable", escName tv, "occurs more than once in", what ]

errNoVariable :: Ident -> String -> Message
errNoVariable tv what = spanInfoMessage tv $ hsep $ map text
  [ "Type constructor or type class identifier", escName tv, "used in", what ]

errUnboundVariable :: Ident -> Message
errUnboundVariable tv = spanInfoMessage tv $
  text "Undefined type variable" <+> text (escName tv)

errBadTypeSynonym :: QualIdent -> Message
errBadTypeSynonym tc = spanInfoMessage tc $ text "Synonym type"
                    <+> text (qualName tc) <+> text "in interface"

errNoElement :: String -> String -> QualIdent -> Ident -> Message
errNoElement what for tc x = spanInfoMessage x $ hsep $ map text
  [ "Hidden", what, escName x, "is not defined for", for, qualName tc ]

errIllegalConstraint :: Constraint -> Message
errIllegalConstraint c = spanInfoMessage c $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints must not contain type quantifiers."
  ]

errIllegalInstanceType :: InstanceType -> Message
errIllegalInstanceType inst = spanInfoMessage inst $ vcat
  [ text "Illegal instance type" <+> pPrint inst
  , text "An instance type must not contain anonymous"
  , text "type variables or type quantifiers."
  ]
