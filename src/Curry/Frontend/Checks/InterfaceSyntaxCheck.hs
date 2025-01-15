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
module Curry.Frontend.Checks.InterfaceSyntaxCheck (intfSyntaxCheck) where

import           Prelude hiding ((<>))
import           Control.Monad            (filterM, liftM, liftM2, when)
import qualified Control.Monad.State as S
import           Data.List                (nub, partition)
import qualified Data.Map as Map          (Map, empty, insert, lookup)
import qualified Data.Set as Set          ( Set, fromList, isSubsetOf, size
                                          , toAscList, union)

import Curry.Frontend.Base.Expr
import Curry.Frontend.Base.Messages       (Message, spanInfoMessage, internalError)
import Curry.Frontend.Base.TopEnv
import Curry.Frontend.Base.Utils          (findMultiples)

import           Curry.Frontend.Env.TypeConstructor
import           Curry.Frontend.Env.Type
import qualified Curry.Frontend.Env.Class as CE

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax

data ISCState = ISCState
  { typeEnv    :: TypeEnv
  , simpClsEnv :: SimpleClassEnv
  , errors     :: [Message]
  }

type ISC = S.State ISCState

type SimpleClassEnv = Map.Map QualIdent [CE.FunDep]

getTypeEnv :: ISC TypeEnv
getTypeEnv = S.gets typeEnv

getSimpleClassEnv :: ISC SimpleClassEnv
getSimpleClassEnv = S.gets simpClsEnv

-- |Report a syntax error
report :: Message -> ISC ()
report msg = S.modify $ \ s -> s { errors = msg : errors s }

intfSyntaxCheck :: Interface -> (Interface, [Message])
intfSyntaxCheck (Interface n is ds o) = (Interface n is ds' o, reverse $ errors s')
  where (ds', s') = S.runState (mapM checkIDecl ds) (ISCState env simpleClsEnv [])
        env = foldr bindType (fmap toTypeKind initTCEnv) ds
        simpleClsEnv = foldr bindClass Map.empty ds

-- The compiler requires information about the arity of each defined type
-- constructor as well as information whether the type constructor
-- denotes an algebraic data type, a renaming type, or a type synonym.
-- The latter must not occur in type expressions in interfaces.

bindType :: IDecl -> TypeEnv -> TypeEnv
bindType (IInfixDecl              _ _ _ _ _) = id
bindType (HidingDataDecl        _ tc _ _ o) = qualBindTopEnv tc' (Data tc' [])
  where tc' = applyOriginPragma o tc
bindType (IDataDecl        _ tc _ _ cs _ o) = qualBindTopEnv tc' $ Data tc' (map constrId cs)
  where tc' = applyOriginPragma o tc
bindType (INewtypeDecl     _ tc _ _ nc _ o) = qualBindTopEnv tc' $ Data tc' [nconstrId nc]
  where tc' = applyOriginPragma o tc
bindType (ITypeDecl           _ tc _ _ _ o) = qualBindTopEnv tc' (Alias tc')
  where tc' = applyOriginPragma o tc
bindType (IFunctionDecl         _ _ _ _ _ _) = id
bindType (HidingClassDecl  _ _ cls _ _ _ o) = qualBindTopEnv cls' $ Class cls' []
  where cls' = applyOriginPragma o cls
bindType (IClassDecl _ _ cls _ _ _ ms hs o) = qualBindTopEnv cls' $ Class cls' (filter (`notElem` hs) (map imethod ms))
  where cls' = applyOriginPragma o cls
bindType (IInstanceDecl      _ _ _ _ _ _ _) = id

-- Adds all information regarding functional dependencies to the simple
-- class env
bindClass :: IDecl -> SimpleClassEnv -> SimpleClassEnv
bindClass (IClassDecl _ _ cls _ tvs fds _ _ _) = let fds' = map (CE.toFunDep tvs) fds
                                                 in  Map.insert cls fds'
bindClass _                                    = id

-- The checks applied to the interface are similar to those performed
-- during syntax checking of type expressions.

checkIDecl :: IDecl -> ISC IDecl
checkIDecl (IInfixDecl  p fix pr op o) = return (IInfixDecl p fix pr op o)
checkIDecl (HidingDataDecl p tc k tvs o) = do
  checkTypeLhs tvs
  return (HidingDataDecl p tc k tvs o)
checkIDecl (IDataDecl p tc k tvs cs hs o) = do
  checkTypeLhs tvs
  checkHiddenType tc (cons ++ labels) hs
  cs' <- mapM (checkConstrDecl tvs) cs
  return $ IDataDecl p tc k tvs cs' hs o
  where cons   = map constrId cs
        labels = nub $ concatMap recordLabels cs
checkIDecl (INewtypeDecl p tc k tvs nc hs o) = do
  checkTypeLhs tvs
  checkHiddenType tc (con : labels) hs
  nc' <- checkNewConstrDecl tvs nc
  return $ INewtypeDecl p tc k tvs nc' hs o
  where con    = nconstrId nc
        labels = nrecordLabels nc
checkIDecl (ITypeDecl p tc k tvs ty o) = do
  checkTypeLhs tvs
  (\ty' -> ITypeDecl p tc k tvs ty' o) <$> checkClosedType tvs ty
checkIDecl (IFunctionDecl p f cm n qty o) =
  (\qty' -> IFunctionDecl p f cm n qty' o) <$> checkQualType qty
checkIDecl (HidingClassDecl p cx qcls k clsvars funDeps o) = do
  checkTypeVars "hiding class declaration" clsvars
  cx' <- checkClosedContext clsvars cx
  funDeps' <- filterM (checkClosedFunDep clsvars) funDeps
  return $ HidingClassDecl p cx' qcls k clsvars funDeps' o
checkIDecl (IClassDecl p cx qcls k clsvars funDeps ms hs o) = do
  checkTypeVars "class declaration" clsvars
  cx' <- checkClosedContext clsvars cx
  funDeps' <- filterM (checkClosedFunDep clsvars) funDeps
  ms' <- mapM checkIMethodDecl ms
  checkHidden (errNoElement "method" "class") qcls (map imethod ms') hs
  return $ IClassDecl p cx' qcls k clsvars funDeps' ms' hs o
checkIDecl (IInstanceDecl p cx qcls inst is m o) = do
  checkClass qcls
  (cx', inst') <- checkQualTypes cx inst
  mapM_ checkInstanceType inst'
  mapM_ (report . errMultipleImplementation . head) $ findMultiples $ map fst is
  return $ IInstanceDecl p cx' qcls inst' is m o

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

checkIMethodDecl :: IMethodDecl -> ISC IMethodDecl
checkIMethodDecl (IMethodDecl p f a qty) =
  IMethodDecl p f a <$> checkQualType qty

-- taken from Leif-Erik Krueger
checkInstanceType :: InstanceType -> ISC ()
checkInstanceType inst =
  when (any isAnonId (typeVars inst) || containsForall inst) $
    report $ errIllegalInstanceType inst


-- take from Leif-Erik Krueger
checkQualType :: QualTypeExpr -> ISC QualTypeExpr
checkQualType (QualTypeExpr spi cx ty) = do
  (cx', ty') <- checkQualTypes cx [ty]
  return $ QualTypeExpr spi cx' (head ty')

-- taken from Leif-Erik Krueger
checkQualTypes :: Context -> [TypeExpr] -> ISC (Context, [TypeExpr])
checkQualTypes cx tys = do
  tys' <- mapM checkType tys
  fvs <- Set.toAscList <$> funDepCoverage cx (Set.fromList $ fv tys)
  cx'  <- checkClosedContext fvs cx
  return (cx', tys')

checkClosedContext :: [Ident] -> Context -> ISC Context
checkClosedContext tvs = mapM (checkClosedConstraint tvs)

checkClosedConstraint :: [Ident] -> Constraint -> ISC Constraint
checkClosedConstraint tvs c = do
  c'@(Constraint _ _ tys) <- checkConstraint c
  mapM_ (checkClosed tvs) tys
  return c'

-- taken from Leif-Erik Krueger
checkConstraint :: Constraint -> ISC Constraint
checkConstraint c@(Constraint spi qcls tys) = do
  checkClass qcls
  when (any containsForall tys) $ report $ errIllegalConstraint c
  Constraint spi qcls `liftM` mapM checkType tys


checkClosedFunDep :: [Ident] -> FunDep -> ISC Bool
checkClosedFunDep clsvars (FunDep _ ltvs rtvs) = do
  let unboundVars = filter (`notElem` clsvars) $ ltvs ++ rtvs
  mapM_ (report . errUnboundVariable) unboundVars
  return $ null unboundVars

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

------------------------------------------------------------------------------
-- Functional dependency coverage
------------------------------------------------------------------------------

qualClassIdent :: QualIdent -> TypeEnv -> Maybe QualIdent
qualClassIdent qcls tEnv = case qualLookupTypeKind qcls tEnv of
  []              -> Nothing
  [Class qcls' _] -> Just qcls'
  [_]             -> Nothing
  _               -> Nothing


funDepCoverage :: Context -> Set.Set Ident -> ISC (Set.Set Ident)
funDepCoverage cx tvs = do
  simpleClsEnv <- getSimpleClassEnv
  tyEnv      <- getTypeEnv
  let tvs' = funDepCoverage' simpleClsEnv tyEnv tvs
  if Set.size tvs' == Set.size tvs
  then return tvs
  else funDepCoverage cx tvs'
  where
   funDepCoverage' clsEnv tyEnv covVars =
    foldr (funDepCoverage'' clsEnv tyEnv) covVars cx

   funDepCoverage'' clsEnv tyEnv c@(Constraint _ cls _) covVars =
    case qualClassIdent cls tyEnv of
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

-- taken from Leif-Erik Krueger
errIllegalConstraint :: Constraint -> Message
errIllegalConstraint c = spanInfoMessage c $ vcat
  [ text "Illegal class constraint" <+> pPrint c
  , text "Constraints must not contain type quantifiers."
  ]


-- taken from Leif-Erik Krueger
errIllegalInstanceType :: InstanceType -> Message
errIllegalInstanceType inst = spanInfoMessage inst $ vcat
  [ text "Illegal instance type" <+> pPrint inst
  , text "An instance type must not contain anonymous"
  , text "type variables or type quantifiers."
  ]
