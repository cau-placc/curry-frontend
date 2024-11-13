{- |
    Module      :  $Header$
    Description :  Checks for wrongly cased identifiers
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Unlike Haskell, Curry is relatively liberal in the identifiers it accepts.
    This is mainly for historical reasons, an artifact of accepting both the
    conventional casings employed in Haskell and Prolog, respectively. To a
    Haskell programmer it may be surprising that

        data x = a

        f :: A -> A
        f X = X

    is valid Curry source code: The first 'x' refers to the name of the data
    type, rather than a type variable, and the second 'A', perhaps more
    counterintuitively, refers to a type variable as opposed to e.g. a type.
    More conventionally, the program would be spelled as

        data X = A

        f :: a -> a
        f x = x

    To avoid this confusion, while still retaining the flexibility of different
    casings, Curry supports different case modes, controlling which casings are
    accepted, warned about or rejected. Using the default case mode (`curry`),
    the frontend would warn about the first program and accept the second one,
    whereas using the case mode `prolog` the second program would error and the
    first program would be accepted.
-}
module Checks.CaseModeCheck (caseModeCheck) where

import Prelude hiding ((<>))
import Data.Char (isAlpha, isUpper, isLower, toUpper, toLower)
import Data.List (sort)
import Control.Monad (unless)
import Control.Monad.State.Strict (State, execState, gets, modify)

import CompilerOpts (CaseMode (..))
import Base.Messages (Message, spanInfoMessage, internalError)
import Curry.Base.Ident (Ident (..), escName)
import Curry.Base.Pretty
import Curry.Syntax

caseModeCheck :: CaseMode -> Module a -> ([Message], [Message])
caseModeCheck cm (Module _ _ _ _ _ _ ds) = runOn state $ checkDecls ds
  where
    state = CmcState
      { caseMode = cm
      , warnings = []
      , errors   = []
      }

data CmcState = CmcState
  { caseMode    :: CaseMode
  , warnings    :: [Message]
  , errors      :: [Message]
  }

type CMCM = State CmcState

report :: Message -> CMCM ()
report m = do
  cm <- gets caseMode
  case cm of
    CaseModeCurry -> modify $ \s -> s { warnings = m : warnings s }
    _             -> modify $ \s -> s { errors   = m : errors s }

ok :: CMCM ()
ok = return ()

-- |Run a 'CMCM' action and return the warnings and errors
runOn :: CmcState -> CMCM a -> ([Message], [Message])
runOn s f = (sort $ warnings s', sort $ errors s')
  where s' = execState f s

-- --------------------------------------------------------------------------
-- Check Case Mode
-- --------------------------------------------------------------------------

-- The following functions traverse the AST and search for (defining)
-- identifiers and check if their names have the appropriate case mode.
checkDecls :: [Decl a] -> CMCM ()
checkDecls = mapM_ checkDecl

checkDecl :: Decl a -> CMCM ()
checkDecl (DataDecl _ tc vs cs _) = do
  checkDataDeclName tc
  mapM_ checkVarName vs
  mapM_ checkConstr cs
checkDecl (NewtypeDecl _ tc vs nc _) = do
  checkDataDeclName tc
  mapM_ checkVarName vs
  checkNewConstr nc
checkDecl (TypeDecl _ tc vs ty) = do
  checkDataDeclName tc
  mapM_ checkVarName vs
  checkTypeExpr ty
checkDecl (TypeSig _ fs qty) = do
  mapM_ checkFuncName fs
  checkQualTypeExpr qty
checkDecl (FunctionDecl _ _ _ eqs) = mapM_ checkEquation eqs
checkDecl (ExternalDecl _ vs) =
  mapM_ (checkFuncName . varIdent) vs
checkDecl (PatternDecl _ t rhs) = do
  checkPattern t
  checkRhs rhs
checkDecl (FreeDecl  _ vs) =
  mapM_ (checkVarName . varIdent) vs
checkDecl (DefaultDecl _ tys) = mapM_ checkTypeExpr tys
checkDecl (ClassDecl _ _ cx cls tvs _ ds) = do
  checkContext cx
  checkClassDeclName cls
  mapM_ checkVarName tvs
  mapM_ checkDecl ds
checkDecl (InstanceDecl _ _ cx _ inst ds) = do
  checkContext cx
  mapM_ checkTypeExpr inst
  mapM_ checkDecl ds
checkDecl _ = ok

checkConstr :: ConstrDecl -> CMCM ()
checkConstr (ConstrDecl _ c tys) = do
  checkConstrName c
  mapM_ checkTypeExpr tys
checkConstr (ConOpDecl  _ ty1 c ty2) = do
  checkTypeExpr ty1
  checkConstrName c
  checkTypeExpr ty2
checkConstr (RecordDecl _ c fs) = do
  checkConstrName c
  mapM_ checkFieldDecl fs

checkFieldDecl :: FieldDecl -> CMCM ()
checkFieldDecl (FieldDecl _ fs ty) = do
  mapM_ checkFuncName fs
  checkTypeExpr ty

checkNewConstr :: NewConstrDecl -> CMCM ()
checkNewConstr (NewConstrDecl _ nc ty) = do
  checkConstrName nc
  checkTypeExpr ty
checkNewConstr (NewRecordDecl _ nc (f, ty)) = do
  checkConstrName nc
  checkFuncName f
  checkTypeExpr ty

checkContext :: Context -> CMCM ()
checkContext = mapM_ checkConstraint

checkConstraint :: Constraint -> CMCM ()
checkConstraint (Constraint _ _ tys) = mapM_ checkTypeExpr tys

checkTypeExpr :: TypeExpr -> CMCM ()
checkTypeExpr (ApplyType _ ty1 ty2) = do
  checkTypeExpr ty1
  checkTypeExpr ty2
checkTypeExpr (VariableType _ tv) = checkVarName tv
checkTypeExpr (TupleType _ tys) = mapM_ checkTypeExpr tys
checkTypeExpr (ListType _ ty) = checkTypeExpr ty
checkTypeExpr (ArrowType _ ty1 ty2) = do
  checkTypeExpr ty1
  checkTypeExpr ty2
checkTypeExpr (ParenType _ ty) = checkTypeExpr ty
checkTypeExpr (ForallType _ tvs ty) = do
  mapM_ checkVarName tvs
  checkTypeExpr ty
checkTypeExpr _ = ok

checkQualTypeExpr :: QualTypeExpr -> CMCM ()
checkQualTypeExpr (QualTypeExpr _ cx ty) = do
  checkContext cx
  checkTypeExpr ty

checkEquation :: Equation a -> CMCM ()
checkEquation (Equation _ _ lhs rhs) = do
  checkLhs lhs
  checkRhs rhs

checkLhs :: Lhs a -> CMCM ()
checkLhs (FunLhs _ f ts) = do
  checkFuncName f
  mapM_ checkPattern ts
checkLhs (OpLhs _ t1 f t2) = do
  checkPattern t1
  checkFuncName f
  checkPattern t2
checkLhs (ApLhs _ lhs ts) = do
  checkLhs lhs
  mapM_ checkPattern ts

checkRhs :: Rhs a -> CMCM ()
checkRhs (SimpleRhs _ _ e ds) = do
  checkExpr e
  mapM_ checkDecl ds
checkRhs (GuardedRhs _ _ es ds) = do
  mapM_ checkCondExpr es
  mapM_ checkDecl ds

checkCondExpr :: CondExpr a -> CMCM ()
checkCondExpr (CondExpr _ g e) = do
  checkExpr g
  checkExpr e

checkPattern :: Pattern a -> CMCM ()
checkPattern (VariablePattern _ _ v) = checkID "variable name" isVarName v
checkPattern (ConstructorPattern _ _ _ ts) =
  mapM_ checkPattern ts
checkPattern (InfixPattern _ _ t1 _ t2) = do
  checkPattern t1
  checkPattern t2
checkPattern (ParenPattern _ t) = checkPattern t
checkPattern (RecordPattern _ _ _ fs) =
  mapM_ checkFieldPattern fs
checkPattern (TuplePattern _ ts) = mapM_ checkPattern ts
checkPattern (ListPattern _ _ ts) = mapM_ checkPattern ts
checkPattern (AsPattern _ v t) = do
  checkID "variable name" isVarName v
  checkPattern t
checkPattern (LazyPattern _ t) = checkPattern t
checkPattern (FunctionPattern _ _ _ ts) = mapM_ checkPattern ts
checkPattern (InfixFuncPattern _ _ t1 _ t2) = do
  checkPattern t1
  checkPattern t2
checkPattern _ = ok

checkExpr :: Expression a -> CMCM ()
checkExpr (Paren _ e) = checkExpr e
checkExpr (Typed _ e qty) = do
  checkExpr e
  checkQualTypeExpr qty
checkExpr (Record _ _ _ fs) = mapM_ checkFieldExpr fs
checkExpr (RecordUpdate _ e fs) = do
  checkExpr e
  mapM_ checkFieldExpr fs
checkExpr (Tuple _ es) = mapM_ checkExpr es
checkExpr (List _ _ es) = mapM_ checkExpr es
checkExpr (ListCompr _ e stms)  = do
  checkExpr e
  mapM_ checkStatement stms
checkExpr (EnumFrom _ e) = checkExpr e
checkExpr (EnumFromThen _ e1 e2) = do
  checkExpr e1
  checkExpr e2
checkExpr (EnumFromTo _ e1 e2) = do
  checkExpr e1
  checkExpr e2
checkExpr (EnumFromThenTo _ e1 e2 e3) = do
  checkExpr e1
  checkExpr e2
  checkExpr e3
checkExpr (UnaryMinus _ e) = checkExpr e
checkExpr (Apply _ e1 e2) = do
  checkExpr e1
  checkExpr e2
checkExpr (InfixApply _ e1 _ e2) = do
  checkExpr e1
  checkExpr e2
checkExpr (LeftSection _ e _) = checkExpr e
checkExpr (RightSection _ _ e) = checkExpr e
checkExpr (Lambda _ ts e) = do
  mapM_ checkPattern ts
  checkExpr e
checkExpr (Let _ _ ds e) = do
  mapM_ checkDecl ds
  checkExpr e
checkExpr (Do _ _ stms e) = do
  mapM_ checkStatement stms
  checkExpr e
checkExpr (IfThenElse _ e1 e2 e3) = do
  checkExpr e1
  checkExpr e2
  checkExpr e3
checkExpr (Case _ _ _ e as) = do
  mapM_ checkAlt as
  checkExpr e
checkExpr _ = ok

checkStatement :: Statement a -> CMCM ()
checkStatement (StmtExpr _    e) = checkExpr e
checkStatement (StmtDecl _ _ ds) = mapM_ checkDecl ds
checkStatement (StmtBind _  t e) = do
  checkPattern t
  checkExpr e

checkAlt :: Alt a -> CMCM ()
checkAlt (Alt _ t rhs) = checkPattern t >> checkRhs rhs

checkFieldPattern :: Field (Pattern a) -> CMCM ()
checkFieldPattern (Field _ _ t) = checkPattern t

checkFieldExpr :: Field (Expression a) -> CMCM ()
checkFieldExpr (Field _ _ e) = checkExpr e

checkVarName :: Ident -> CMCM ()
checkVarName = checkID "variable name" isVarName

checkFuncName :: Ident -> CMCM ()
checkFuncName = checkID "function name" isFuncName

checkConstrName :: Ident -> CMCM ()
checkConstrName = checkID "constructor name" isConstrName

checkClassDeclName :: Ident -> CMCM ()
checkClassDeclName = checkID "class declaration name" isClassDeclName

checkDataDeclName :: Ident -> CMCM ()
checkDataDeclName = checkID "data declaration name" isDataDeclName

checkID :: String -> (CaseMode -> String -> Bool) -> Ident -> CMCM ()
checkID what f i@(Ident _ name _) = do
  c <- gets caseMode

  unless (f c name) (report $ wrongCaseMode what i c)

isVarName :: CaseMode -> String -> Bool
isVarName CaseModeProlog  (x:_) | isAlpha x = isUpper x
isVarName CaseModeGoedel  (x:_) | isAlpha x = isLower x
isVarName CaseModeHaskell (x:_) | isAlpha x = isLower x
isVarName CaseModeCurry   (x:_) | isAlpha x = isLower x
isVarName _               _     = True

isFuncName :: CaseMode -> String -> Bool
isFuncName CaseModeHaskell (x:_) | isAlpha x = isLower x
isFuncName CaseModeGoedel  (x:_) | isAlpha x = isUpper x
isFuncName CaseModeProlog  (x:_) | isAlpha x = isLower x
isFuncName CaseModeCurry   (x:_) | isAlpha x = isLower x
isFuncName _               _     = True

isConstrName :: CaseMode -> String -> Bool
isConstrName = isDataDeclName

isClassDeclName :: CaseMode -> String -> Bool
isClassDeclName = isDataDeclName

isDataDeclName :: CaseMode -> String -> Bool
isDataDeclName CaseModeProlog  (x:_) | isAlpha x = isLower x
isDataDeclName CaseModeGoedel  (x:_) | isAlpha x = isUpper x
isDataDeclName CaseModeHaskell (x:_) | isAlpha x = isUpper x
isDataDeclName CaseModeCurry   (x:_) | isAlpha x = isUpper x
isDataDeclName _               _     = True

wrongCaseMode :: String -> Ident -> CaseMode -> Message
wrongCaseMode what i@(Ident _ name _ ) c = spanInfoMessage i $
  text "Symbol" <+> text (escName i) <+> text "is a" <+> text what <> comma <+>
  text "but the selected case mode is" <+> text (escapeCaseMode c) <> comma <+>
  text "try renaming to" <+> text (caseSuggestion name) <+> text "instead"

caseSuggestion :: String -> String
caseSuggestion (x:xs) | isLower x = toUpper x : xs
                      | isUpper x = toLower x : xs
caseSuggestion _      = internalError
 "Checks.CaseModeCheck.caseSuggestion: Identifier starts with illegal Symbol"

escapeCaseMode :: CaseMode -> String
escapeCaseMode CaseModeCurry   = "`curry`"
escapeCaseMode CaseModeFree    = "`free`"
escapeCaseMode CaseModeHaskell = "`haskell`"
escapeCaseMode CaseModeProlog  = "`prolog`"
escapeCaseMode CaseModeGoedel  = "`goedel`"
