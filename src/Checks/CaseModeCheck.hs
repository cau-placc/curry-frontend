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
{-# LANGUAGE CPP #-}
module Checks.CaseModeCheck (caseModeCheck) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import Base.Messages (Message, spanInfoMessage, internalError)
import CompilerOpts (CaseMode (..))
import Control.Monad (unless)
import Control.Monad.State.Strict (State, execState, gets, modify)
import Curry.Base.Ident (Ident (..), escName)
import Curry.Base.Pretty
import Curry.Syntax
import Data.Char (isAlpha, isUpper, isLower, toUpper, toLower)
import Data.List (sort)

caseModeCheck :: CaseMode -> Module a -> ([Message], [Message])
caseModeCheck cm (Module _ _ _ _ _ _ ds) = runOn state $ checkCaseMode ds
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
report w = modify $ \ s -> s { warnings = w : warnings s }

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
checkCaseMode :: [Decl a] -> CMCM ()
checkCaseMode = mapM_ checkCaseModeDecl

checkCaseModeDecl :: Decl a -> CMCM ()
checkCaseModeDecl (DataDecl _ tc vs cs _) = do
  checkCaseModeID isDataDeclName tc
  mapM_ (checkCaseModeID isVarName) vs
  mapM_ checkCaseModeConstr cs
checkCaseModeDecl (NewtypeDecl _ tc vs nc _) = do
  checkCaseModeID isDataDeclName tc
  mapM_ (checkCaseModeID isVarName) vs
  checkCaseModeNewConstr nc
checkCaseModeDecl (TypeDecl _ tc vs ty) = do
  checkCaseModeID isDataDeclName tc
  mapM_ (checkCaseModeID isVarName) vs
  checkCaseModeTypeExpr ty
checkCaseModeDecl (TypeSig _ fs qty) = do
  mapM_ (checkCaseModeID isFuncName) fs
  checkCaseModeQualTypeExpr qty
checkCaseModeDecl (FunctionDecl _ _ f eqs) = do
  checkCaseModeID isFuncName f
  mapM_ checkCaseModeEquation eqs
checkCaseModeDecl (ExternalDecl _ vs) =
  mapM_ (checkCaseModeID isFuncName . varIdent) vs
checkCaseModeDecl (PatternDecl _ t rhs) = do
  checkCaseModePattern t
  checkCaseModeRhs rhs
checkCaseModeDecl (FreeDecl  _ vs) =
  mapM_ (checkCaseModeID isVarName . varIdent) vs
checkCaseModeDecl (DefaultDecl _ tys) = mapM_ checkCaseModeTypeExpr tys
checkCaseModeDecl (ClassDecl _ _ cx cls tv ds) = do
  checkCaseModeContext cx
  checkCaseModeID isClassDeclName cls
  checkCaseModeID isVarName tv
  mapM_ checkCaseModeDecl ds
checkCaseModeDecl (InstanceDecl _ _ cx _ inst ds) = do
  checkCaseModeContext cx
  checkCaseModeTypeExpr inst
  mapM_ checkCaseModeDecl ds
checkCaseModeDecl _ = ok

checkCaseModeConstr :: ConstrDecl -> CMCM ()
checkCaseModeConstr (ConstrDecl _ c tys) = do
  checkCaseModeID isConstrName c
  mapM_ checkCaseModeTypeExpr tys
checkCaseModeConstr (ConOpDecl  _ ty1 c ty2) = do
  checkCaseModeTypeExpr ty1
  checkCaseModeID isConstrName c
  checkCaseModeTypeExpr ty2
checkCaseModeConstr (RecordDecl _ c fs) = do
  checkCaseModeID isConstrName c
  mapM_ checkCaseModeFieldDecl fs

checkCaseModeFieldDecl :: FieldDecl -> CMCM ()
checkCaseModeFieldDecl (FieldDecl _ fs ty) = do
  mapM_ (checkCaseModeID isFuncName) fs
  checkCaseModeTypeExpr ty

checkCaseModeNewConstr :: NewConstrDecl -> CMCM ()
checkCaseModeNewConstr (NewConstrDecl _ nc ty) = do
  checkCaseModeID isConstrName nc
  checkCaseModeTypeExpr ty
checkCaseModeNewConstr (NewRecordDecl _ nc (f, ty)) = do
  checkCaseModeID isConstrName nc
  checkCaseModeID isFuncName f
  checkCaseModeTypeExpr ty

checkCaseModeContext :: Context -> CMCM ()
checkCaseModeContext = mapM_ checkCaseModeConstraint

checkCaseModeConstraint :: Constraint -> CMCM ()
checkCaseModeConstraint (Constraint _ _ ty) = checkCaseModeTypeExpr ty

checkCaseModeTypeExpr :: TypeExpr -> CMCM ()
checkCaseModeTypeExpr (ApplyType _ ty1 ty2) = do
  checkCaseModeTypeExpr ty1
  checkCaseModeTypeExpr ty2
checkCaseModeTypeExpr (VariableType _ tv) = checkCaseModeID isVarName tv
checkCaseModeTypeExpr (TupleType _ tys) = mapM_ checkCaseModeTypeExpr tys
checkCaseModeTypeExpr (ListType _ ty) = checkCaseModeTypeExpr ty
checkCaseModeTypeExpr (ArrowType _ ty1 ty2) = do
  checkCaseModeTypeExpr ty1
  checkCaseModeTypeExpr ty2
checkCaseModeTypeExpr (ParenType _ ty) = checkCaseModeTypeExpr ty
checkCaseModeTypeExpr (ForallType _ tvs ty) = do
  mapM_ (checkCaseModeID isVarName) tvs
  checkCaseModeTypeExpr ty
checkCaseModeTypeExpr _ = ok

checkCaseModeQualTypeExpr :: QualTypeExpr -> CMCM ()
checkCaseModeQualTypeExpr (QualTypeExpr _ cx ty) = do
  checkCaseModeContext cx
  checkCaseModeTypeExpr ty

checkCaseModeEquation :: Equation a -> CMCM ()
checkCaseModeEquation (Equation _ lhs rhs) = do
  checkCaseModeLhs lhs
  checkCaseModeRhs rhs

checkCaseModeLhs :: Lhs a -> CMCM ()
checkCaseModeLhs (FunLhs _ f ts) = do
  checkCaseModeID isFuncName f
  mapM_ checkCaseModePattern ts
checkCaseModeLhs (OpLhs _ t1 f t2) = do
  checkCaseModePattern t1
  checkCaseModeID isFuncName f
  checkCaseModePattern t2
checkCaseModeLhs (ApLhs _ lhs ts) = do
  checkCaseModeLhs lhs
  mapM_ checkCaseModePattern ts

checkCaseModeRhs :: Rhs a -> CMCM ()
checkCaseModeRhs (SimpleRhs _ _ e ds) = do
  checkCaseModeExpr e
  mapM_ checkCaseModeDecl ds
checkCaseModeRhs (GuardedRhs _ _ es ds) = do
  mapM_ checkCaseModeCondExpr es
  mapM_ checkCaseModeDecl ds

checkCaseModeCondExpr :: CondExpr a -> CMCM ()
checkCaseModeCondExpr (CondExpr _ g e) = do
  checkCaseModeExpr g
  checkCaseModeExpr e

checkCaseModePattern :: Pattern a -> CMCM ()
checkCaseModePattern (VariablePattern _ _ v) = checkCaseModeID isVarName v
checkCaseModePattern (ConstructorPattern _ _ _ ts) =
  mapM_ checkCaseModePattern ts
checkCaseModePattern (InfixPattern _ _ t1 _ t2) = do
  checkCaseModePattern t1
  checkCaseModePattern t2
checkCaseModePattern (ParenPattern _ t) = checkCaseModePattern t
checkCaseModePattern (RecordPattern _ _ _ fs) =
  mapM_ checkCaseModeFieldPattern fs
checkCaseModePattern (TuplePattern _ ts) = mapM_ checkCaseModePattern ts
checkCaseModePattern (ListPattern _ _ ts) = mapM_ checkCaseModePattern ts
checkCaseModePattern (AsPattern _ v t) = do
  checkCaseModeID isVarName v
  checkCaseModePattern t
checkCaseModePattern (LazyPattern _ t) = checkCaseModePattern t
checkCaseModePattern (FunctionPattern _ _ _ ts) = mapM_ checkCaseModePattern ts
checkCaseModePattern (InfixFuncPattern _ _ t1 _ t2) = do
  checkCaseModePattern t1
  checkCaseModePattern t2
checkCaseModePattern _ = ok

checkCaseModeExpr :: Expression a -> CMCM ()
checkCaseModeExpr (Paren _ e) = checkCaseModeExpr e
checkCaseModeExpr (Typed _ e qty) = do
  checkCaseModeExpr e
  checkCaseModeQualTypeExpr qty
checkCaseModeExpr (Record _ _ _ fs) = mapM_ checkCaseModeFieldExpr fs
checkCaseModeExpr (RecordUpdate _ e fs) = do
  checkCaseModeExpr e
  mapM_ checkCaseModeFieldExpr fs
checkCaseModeExpr (Tuple _ es) = mapM_ checkCaseModeExpr es
checkCaseModeExpr (List _ _ es) = mapM_ checkCaseModeExpr es
checkCaseModeExpr (ListCompr _ e stms)  = do
  checkCaseModeExpr e
  mapM_ checkCaseModeStatement stms
checkCaseModeExpr (EnumFrom _ e) = checkCaseModeExpr e
checkCaseModeExpr (EnumFromThen _ e1 e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (EnumFromTo _ e1 e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (EnumFromThenTo _ e1 e2 e3) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
  checkCaseModeExpr e3
checkCaseModeExpr (UnaryMinus _ e) = checkCaseModeExpr e
checkCaseModeExpr (Apply _ e1 e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (InfixApply _ e1 _ e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (LeftSection _ e _) = checkCaseModeExpr e
checkCaseModeExpr (RightSection _ _ e) = checkCaseModeExpr e
checkCaseModeExpr (Lambda _ ts e) = do
  mapM_ checkCaseModePattern ts
  checkCaseModeExpr e
checkCaseModeExpr (Let _ _ ds e) = do
  mapM_ checkCaseModeDecl ds
  checkCaseModeExpr e
checkCaseModeExpr (Do _ _ stms e) = do
  mapM_ checkCaseModeStatement stms
  checkCaseModeExpr e
checkCaseModeExpr (IfThenElse _ e1 e2 e3) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
  checkCaseModeExpr e3
checkCaseModeExpr (Case _ _ _ e as) = do
  mapM_ checkCaseModeAlt as
  checkCaseModeExpr e
checkCaseModeExpr _ = ok

checkCaseModeStatement :: Statement a -> CMCM ()
checkCaseModeStatement (StmtExpr _    e) = checkCaseModeExpr e
checkCaseModeStatement (StmtDecl _ _ ds) = mapM_ checkCaseModeDecl ds
checkCaseModeStatement (StmtBind _  t e) = do
  checkCaseModePattern t
  checkCaseModeExpr e

checkCaseModeAlt :: Alt a -> CMCM ()
checkCaseModeAlt (Alt _ t rhs) = checkCaseModePattern t >> checkCaseModeRhs rhs

checkCaseModeFieldPattern :: Field (Pattern a) -> CMCM ()
checkCaseModeFieldPattern (Field _ _ t) = checkCaseModePattern t

checkCaseModeFieldExpr :: Field (Expression a) -> CMCM ()
checkCaseModeFieldExpr (Field _ _ e) = checkCaseModeExpr e

checkCaseModeID :: (CaseMode -> String -> Bool) -> Ident -> CMCM ()
checkCaseModeID f i@(Ident _ name _) = do
  c <- gets caseMode

  unless (f c name) (report $ warnCaseMode i c)

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

warnCaseMode :: Ident -> CaseMode -> Message
warnCaseMode i@(Ident _ name _ ) c = spanInfoMessage i $
  text "Wrong case mode in symbol" <+> text (escName i) <+>
  text "due to selected case mode" <+> text (escapeCaseMode c) <> comma <+>
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
