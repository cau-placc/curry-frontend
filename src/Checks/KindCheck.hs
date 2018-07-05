{- |
    Module      :  $Header$
    Description :  Checks type definitions
    Copyright   :  (c) 2000 - 2007 Wolfgang Lux
                                   Martin Engelke
                                   Björn Peemöller
                       2014 - 2015 Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After the source file has been parsed and all modules have been
   imported, the compiler first performs kind checking on all type
   definitions and signatures. Because Curry currently does not support
   type classes, kind checking is rather trivial. All types must be of
   first order kind (*), i.e., all type constructor applications
   must be saturated.

   During kind checking, this module will also disambiguate nullary type
   constructors and type variables which -- in contrast to Haskell -- is
   not possible on purely syntactic criteria. In addition it is checked
   that all type constructors and type variables occurring on the right
   hand side of a type declaration are actually defined and no identifier
   is defined more than once.
-}
{-# LANGUAGE CPP #-}
module Checks.KindCheck (kindCheck) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>))
#endif
import           Control.Monad            (unless, when)
import qualified Control.Monad.State as S (State, runState, gets, modify)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.Messages (Message, posMessage, internalError)
import Base.TopEnv
import Base.Utils (findMultiples)

import Env.TypeConstructor (TCEnv, tcArity)

-- In order to check type constructor applications, the compiler
-- maintains an environment containing the kind information for all type
-- constructors. The function 'kindCheck' first initializes this
-- environment by filtering out the arity of each type constructor from
-- the imported type environment. Next, the arities of all locally
-- defined type constructors are inserted into the environment, and,
-- finally, the declarations are checked within this environment.

kindCheck :: TCEnv -> Module -> (Module, [Message])
kindCheck tcEnv mdl@(Module _ m _ _ ds) =
  case findMultiples $ map typeConstr tds of
    []  -> runKCM (checkModule mdl) state
    tss -> (mdl, map errMultipleDeclaration tss)
  where tds   = filter isTypeDecl ds
        kEnv  = foldr (bindKind m) (fmap tcArity tcEnv) tds
        state = KCState m kEnv []

-- Kind Check Monad
type KCM = S.State KCState

-- |Internal state of the Kind Check
data KCState = KCState
  { moduleIdent :: ModuleIdent
  , kindEnv     :: KindEnv
  , errors      :: [Message]
  }

runKCM :: KCM a -> KCState -> (a, [Message])
runKCM kcm s = let (a, s') = S.runState kcm s in (a, reverse $ errors s')

getModuleIdent :: KCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getKindEnv :: KCM KindEnv
getKindEnv = S.gets kindEnv

report :: Message -> KCM ()
report err = S.modify (\ s -> s { errors = err : errors s })

-- The kind environment only needs to record the arity
-- of each type constructor.
type KindEnv = TopEnv Int

bindKind :: ModuleIdent -> Decl -> KindEnv -> KindEnv
bindKind m (DataDecl    _ tc tvs _) = bindKind' m tc tvs
bindKind m (NewtypeDecl _ tc tvs _) = bindKind' m tc tvs
bindKind m (TypeDecl    _ tc tvs _) = bindKind' m tc tvs
bindKind _ _                        = id

bindKind' :: ModuleIdent -> Ident -> [Ident] -> KindEnv -> KindEnv
bindKind' m tc tvs = bindTopEnv tc arity . qualBindTopEnv qtc arity
  where arity = length tvs
        qtc   = qualifyWith m tc

lookupKind :: Ident -> KindEnv -> [Int]
lookupKind = lookupTopEnv

qualLookupKind :: QualIdent -> KindEnv -> [Int]
qualLookupKind = qualLookupTopEnv

checkModule :: Module -> KCM Module
checkModule (Module ps m es is ds) = Module ps m es is <$> mapM checkDecl ds

-- When type declarations are checked, the compiler will allow anonymous
-- type variables on the left hand side of the declaration, but not on
-- the right hand side. Function and pattern declarations must be
-- traversed because they can contain local type signatures.

checkDecl :: Decl -> KCM Decl
checkDecl (DataDecl     p tc tvs cs) = do
  tvs' <- checkTypeLhs tvs
  cs'  <- mapM (checkConstrDecl tvs') cs
  return $ DataDecl p tc tvs' cs'
checkDecl (NewtypeDecl  p tc tvs nc) = do
  tvs' <- checkTypeLhs tvs
  nc'  <- checkNewConstrDecl tvs' nc
  return $ NewtypeDecl p tc tvs' nc'
checkDecl (TypeDecl     p tc tvs ty) = do
  tvs' <- checkTypeLhs tvs
  ty'  <- checkClosedType tvs' ty
  return $ TypeDecl p tc tvs' ty'
checkDecl (TypeSig          p vs ty) = TypeSig p vs          <$> checkType ty
checkDecl (FunctionDecl     p f eqs) = FunctionDecl p f      <$>
                                       mapM checkEquation eqs
checkDecl (PatternDecl      p t rhs) = PatternDecl p t       <$> checkRhs rhs
checkDecl (ForeignDecl p cc ie f ty) = ForeignDecl p cc ie f <$> checkType ty
checkDecl d                          = return d

checkConstrDecl :: [Ident] -> ConstrDecl -> KCM ConstrDecl
checkConstrDecl tvs (ConstrDecl p evs c tys) = do
  evs' <- checkTypeLhs evs
  tys' <- mapM (checkClosedType (evs' ++ tvs)) tys
  return $ ConstrDecl p evs' c tys'
checkConstrDecl tvs (ConOpDecl p evs ty1 op ty2) = do
  evs' <- checkTypeLhs evs
  let tvs' = evs' ++ tvs
  ty1' <- checkClosedType tvs' ty1
  ty2' <- checkClosedType tvs' ty2
  return $ ConOpDecl p evs' ty1' op ty2'
checkConstrDecl tvs (RecordDecl p evs c fs) = do
  evs' <- checkTypeLhs evs
  fs'  <- mapM (checkFieldDecl (evs' ++ tvs)) fs
  return $ RecordDecl p evs' c fs'

checkFieldDecl :: [Ident] -> FieldDecl -> KCM FieldDecl
checkFieldDecl tvs (FieldDecl p ls ty) =
  FieldDecl p ls <$> checkClosedType tvs ty

checkNewConstrDecl :: [Ident] -> NewConstrDecl -> KCM NewConstrDecl
checkNewConstrDecl tvs (NewConstrDecl p evs c ty) = do
  evs' <- checkTypeLhs evs
  ty'  <- checkClosedType (evs' ++ tvs) ty
  return $ NewConstrDecl p evs' c ty'
checkNewConstrDecl tvs (NewRecordDecl p evs c (l, ty)) = do
  evs' <- checkTypeLhs evs
  ty'  <- checkClosedType (evs' ++ tvs) ty
  return $ NewRecordDecl p evs' c (l, ty')

-- |Check the left-hand-side of a type declaration for
-- * Anonymous type variables are allowed
-- * only type variables (no type constructors)
-- * linearity
checkTypeLhs :: [Ident] -> KCM [Ident]
checkTypeLhs []         = return []
checkTypeLhs (tv : tvs) = do
  unless (isAnonId tv) $ do
    isTyCons <- (not . null . lookupKind tv) <$> getKindEnv
    when isTyCons        $ report $ errNoVariable tv
    when (tv `elem` tvs) $ report $ errNonLinear  tv
  (tv:) <$> checkTypeLhs tvs

-- Checking expressions is rather straight forward. The compiler must
-- only traverse the structure of expressions in order to find local
-- declaration groups.

checkEquation :: Equation -> KCM Equation
checkEquation (Equation p lhs rhs) = Equation p lhs <$> checkRhs rhs

checkRhs :: Rhs -> KCM Rhs
checkRhs (SimpleRhs p e ds) = SimpleRhs p <$> checkExpr e <*> mapM checkDecl ds
checkRhs (GuardedRhs es ds) = GuardedRhs  <$> mapM checkCondExpr es
                                          <*> mapM checkDecl ds

checkCondExpr :: CondExpr -> KCM CondExpr
checkCondExpr (CondExpr p g e) = CondExpr p <$> checkExpr g <*> checkExpr e

checkExpr :: Expression -> KCM Expression
checkExpr l@(Literal         _) = return l
checkExpr v@(Variable        _) = return v
checkExpr c@(Constructor     _) = return c
checkExpr (Paren             e) = Paren <$> checkExpr e
checkExpr (Typed          e ty) = Typed <$> checkExpr e <*> checkType ty
checkExpr (Record         c fs) = Record c <$> mapM checkFieldExpr fs
checkExpr (RecordUpdate   e fs) = RecordUpdate <$> checkExpr e
                                               <*> mapM checkFieldExpr fs
checkExpr (Tuple          p es) = Tuple p <$> mapM checkExpr es
checkExpr (List           p es) = List  p <$> mapM checkExpr es
checkExpr (ListCompr    p e qs) = ListCompr p <$> checkExpr e
                                              <*> mapM checkStmt qs
checkExpr (EnumFrom          e) = EnumFrom     <$> checkExpr e
checkExpr (EnumFromThen  e1 e2) = EnumFromThen <$> checkExpr e1 <*> checkExpr e2
checkExpr (EnumFromTo    e1 e2) = EnumFromTo   <$> checkExpr e1 <*> checkExpr e2
checkExpr (EnumFromThenTo e1 e2 e3) = EnumFromThenTo <$> checkExpr e1
                                      <*> checkExpr e2 <*> checkExpr e3
checkExpr (UnaryMinus     op e) = UnaryMinus op <$> checkExpr e
checkExpr (Apply         e1 e2) = Apply <$> checkExpr e1 <*> checkExpr e2
checkExpr (InfixApply e1 op e2) = (\f1 f2 -> InfixApply f1 op f2) <$>
                                  checkExpr e1 <*> checkExpr e2
checkExpr (LeftSection    e op) = flip LeftSection op <$> checkExpr e
checkExpr (RightSection   op e) = RightSection op <$> checkExpr e
checkExpr (Lambda       r ts e) = Lambda r ts <$> checkExpr e
checkExpr (Let            ds e) = Let <$> mapM checkDecl ds <*> checkExpr e
checkExpr (Do            sts e) = Do  <$> mapM checkStmt sts <*> checkExpr e
checkExpr (IfThenElse r e1 e2 e3) = IfThenElse r <$> checkExpr e1
                                     <*> checkExpr e2 <*> checkExpr e3
checkExpr (Case    r ct e alts) = Case r ct <$> checkExpr e
                                            <*> mapM checkAlt alts

checkStmt :: Statement -> KCM Statement
checkStmt (StmtExpr   p e) = StmtExpr p   <$> checkExpr e
checkStmt (StmtBind p t e) = StmtBind p t <$> checkExpr e
checkStmt (StmtDecl    ds) = StmtDecl     <$> mapM checkDecl ds

checkAlt :: Alt -> KCM Alt
checkAlt (Alt p t rhs) = Alt p t <$> checkRhs rhs

checkFieldExpr :: Field Expression -> KCM (Field Expression)
checkFieldExpr (Field p l e) = Field p l <$> checkExpr e

-- The parser cannot distinguish unqualified nullary type constructors
-- and type variables. Therefore, if the compiler finds an unbound
-- identifier in a position where a type variable is admissible, it will
-- interpret the identifier as such.

checkClosedType :: [Ident] -> TypeExpr -> KCM TypeExpr
checkClosedType tvs ty = do
  ty' <- checkType ty
  checkClosed tvs ty'
  return ty'

checkType :: TypeExpr -> KCM TypeExpr
checkType c@(ConstructorType tc tys) = do
  m <- getModuleIdent
  kEnv <- getKindEnv
  case qualLookupKind tc kEnv of
    []
      | not (isQualified tc) && null tys ->
          return $ VariableType $ unqualify tc
      | otherwise -> report (errUndefinedType tc) >> return c
    [n]
      | n == n'   -> ConstructorType tc <$> mapM checkType tys
      | otherwise -> report (errWrongArity tc n n') >> return c
    _ -> case qualLookupKind (qualQualify m tc) kEnv of
      [n]
        | n == n'   -> ConstructorType tc <$> mapM checkType tys
        | otherwise -> report (errWrongArity tc n n') >> return c
      _ -> report (errAmbiguousType tc) >> return c
 where n' = length tys
checkType v@(VariableType tv)
  | isAnonId tv = return v
  | otherwise   = checkType $ ConstructorType (qualify tv) []
checkType (TupleType     tys) = TupleType  <$> mapM checkType tys
checkType (ListType       ty) = ListType   <$> checkType ty
checkType (ArrowType ty1 ty2) = ArrowType  <$> checkType ty1 <*> checkType ty2
checkType (ParenType      ty) = ParenType  <$> checkType ty

checkClosed :: [Ident] -> TypeExpr -> KCM ()
checkClosed tvs (ConstructorType _ tys) = mapM_ (checkClosed tvs) tys
checkClosed tvs (VariableType       tv) = do
  when (isAnonId tv || tv `notElem` tvs) $ report $ errUnboundVariable tv
checkClosed tvs (TupleType         tys) = mapM_ (checkClosed tvs) tys
checkClosed tvs (ListType           ty) = checkClosed tvs ty
checkClosed tvs (ArrowType     ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (ParenType          ty) = checkClosed tvs ty

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

typeConstr :: Decl -> Ident
typeConstr (DataDecl    _ tc _ _) = tc
typeConstr (NewtypeDecl _ tc _ _) = tc
typeConstr (TypeDecl    _ tc _ _) = tc
typeConstr _ = internalError "KindCheck.typeConstr: no type declaration"

-- ---------------------------------------------------------------------------
-- Error messages:
-- ---------------------------------------------------------------------------

errUndefinedType :: QualIdent -> Message
errUndefinedType tc = posMessage tc $ hsep $ map text
  ["Undefined type", qualName tc]

errAmbiguousType :: QualIdent -> Message
errAmbiguousType tc = posMessage tc $ hsep $ map text
  ["Ambiguous type", qualName tc]

errMultipleDeclaration :: [Ident] -> Message
errMultipleDeclaration []     = internalError
  "KindCheck.errMultipleDeclaration: empty list"
errMultipleDeclaration (i:is) = posMessage i $
  text "Multiple declarations for type" <+> text (escName i)
  <+> text "at:" $+$
  nest 2 (vcat (map showPos (i:is)))
  where showPos = text . showLine . idPosition

errNonLinear :: Ident -> Message
errNonLinear tv = posMessage tv $ hsep $ map text
  [ "Type variable", idName tv
  , "occurs more than once on left hand side of type declaration"]

errNoVariable :: Ident -> Message
errNoVariable tv = posMessage tv $ hsep $ map text
  [ "Type constructor", idName tv
  , "used in left hand side of type declaration"]

errWrongArity :: QualIdent -> Int -> Int -> Message
errWrongArity tc arity argc = posMessage tc $
  text "Type constructor" <+> text (qualName tc)
  <+> text "expects" <+> text (arguments arity)
  <> comma <+> text "but is applied to" <+> text (show argc)
  where arguments 0 = "no arguments"
        arguments 1 = "1 argument"
        arguments n = show n ++ " arguments"

errUnboundVariable :: Ident -> Message
errUnboundVariable tv = posMessage tv $ hsep $ map text
  ["Unbound type variable", idName tv]
