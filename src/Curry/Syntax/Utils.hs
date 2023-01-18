{- |
    Module      :  $Header$
    Description :  Utility functions for Curry's abstract syntax
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2014 Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides some utility functions for working with the
    abstract syntax tree of Curry.
-}

module Curry.Syntax.Utils
  ( hasLanguageExtension, knownExtensions
  , isTopDecl, isBlockDecl
  , isTypeSig, infixOp, isTypeDecl, isValueDecl, isInfixDecl
  , isDefaultDecl, isClassDecl, isTypeOrClassDecl, isInstanceDecl
  , isFunctionDecl, isExternalDecl, patchModuleId
  , isVariablePattern
  , isVariableType, isSimpleType
  , typeConstr, typeVariables, varIdent
  , flatLhs, eqnArity, fieldLabel, fieldTerm, field2Tuple, opName
  , funDecl, mkEquation, simpleRhs, patDecl, varDecl, constrPattern, caseAlt
  , mkLet, mkVar, mkCase, mkLambda
  , apply, unapply
  , constrId, nconstrId
  , nconstrType
  , recordLabels, nrecordLabels
  , methods, impls, imethod, imethodArity
  , shortenModuleAST
  ) where

import Control.Monad.State

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Files.Filenames (takeBaseName)
import Curry.Syntax.Extension
import Curry.Syntax.Type

-- |Check whether a 'Module' has a specific 'KnownExtension' enabled by a pragma
hasLanguageExtension :: Module a -> KnownExtension -> Bool
hasLanguageExtension mdl ext = ext `elem` knownExtensions mdl

-- |Extract all known extensions from a 'Module'
knownExtensions :: Module a -> [KnownExtension]
knownExtensions (Module _ _ ps _ _ _ _) =
  [ e | LanguagePragma _ exts <- ps, KnownExtension _ e <- exts]

-- |Replace the generic module name @main@ with the module name derived
-- from the 'FilePath' of the module.
patchModuleId :: FilePath -> Module a -> Module a
patchModuleId fn m@(Module spi li ps mid es is ds)
  | mid == mainMIdent = Module spi li ps (mkMIdent [takeBaseName fn]) es is ds
  | otherwise         = m

-- |Is the declaration a top declaration?
isTopDecl :: Decl a -> Bool
isTopDecl = not . isBlockDecl

-- |Is the declaration a block declaration?
isBlockDecl :: Decl a -> Bool
isBlockDecl = liftM3 ((.) (||) . (||)) isInfixDecl isTypeSig isValueDecl

-- |Is the declaration an infix declaration?
isInfixDecl :: Decl a -> Bool
isInfixDecl (InfixDecl _ _ _ _) = True
isInfixDecl _                   = False

-- |Is the declaration a type declaration?
isTypeDecl :: Decl a -> Bool
isTypeDecl (DataDecl     _ _ _ _ _) = True
isTypeDecl (ExternalDataDecl _ _ _) = True
isTypeDecl (NewtypeDecl  _ _ _ _ _) = True
isTypeDecl (TypeDecl       _ _ _ _) = True
isTypeDecl _                        = False

-- |Is the declaration a default declaration?
isDefaultDecl :: Decl a -> Bool
isDefaultDecl (DefaultDecl _ _) = True
isDefaultDecl _                 = False

-- |Is the declaration a class declaration?
isClassDecl :: Decl a -> Bool
isClassDecl (ClassDecl _ _ _ _ _ _ _) = True
isClassDecl _                         = False

-- |Is the declaration a type or a class declaration?
isTypeOrClassDecl :: Decl a -> Bool
isTypeOrClassDecl = liftM2 (||) isTypeDecl isClassDecl

-- |Is the declaration an instance declaration?
isInstanceDecl :: Decl a -> Bool
isInstanceDecl (InstanceDecl _ _ _ _ _ _) = True
isInstanceDecl _                          = False

-- |Is the declaration a type signature?
isTypeSig :: Decl a -> Bool
isTypeSig (TypeSig           _ _ _) = True
isTypeSig _                         = False

-- |Is the declaration a value declaration?
isValueDecl :: Decl a -> Bool
isValueDecl (FunctionDecl    _ _ _ _) = True
isValueDecl (ExternalDecl        _ _) = True
isValueDecl (PatternDecl       _ _ _) = True
isValueDecl (FreeDecl            _ _) = True
isValueDecl _                         = False

-- |Is the declaration a function declaration?
isFunctionDecl :: Decl a -> Bool
isFunctionDecl (FunctionDecl _ _ _ _) = True
isFunctionDecl _                      = False

-- |Is the declaration an external declaration?
isExternalDecl :: Decl a -> Bool
isExternalDecl (ExternalDecl _ _) = True
isExternalDecl _                  = False

-- |Is the pattern semantically equivalent to a variable pattern?
isVariablePattern :: Pattern a -> Bool
isVariablePattern (VariablePattern _ _ _) = True
isVariablePattern (ParenPattern    _   t) = isVariablePattern t
isVariablePattern (AsPattern       _ _ t) = isVariablePattern t
isVariablePattern (LazyPattern     _   _) = True
isVariablePattern _                       = False

-- |Is a type expression a type variable?
isVariableType :: TypeExpr -> Bool
isVariableType (VariableType _ _) = True
isVariableType _                  = False

-- |Is a type expression simple, i.e., is it of the form T u_1 ... u_n,
-- where T is a type constructor and u_1 ... u_n are type variables?
isSimpleType :: TypeExpr -> Bool
isSimpleType (ConstructorType _ _) = True
isSimpleType (ApplyType _ ty1 ty2) = isSimpleType ty1 && isVariableType ty2
isSimpleType (VariableType   _  _) = False
isSimpleType (TupleType    _  tys) = all isVariableType tys
isSimpleType (ListType      _  ty) = isVariableType ty
isSimpleType (ArrowType _ ty1 ty2) = isVariableType ty1 && isVariableType ty2
isSimpleType (ParenType     _  ty) = isSimpleType ty
isSimpleType (ForallType    _ _ _) = False

-- |Return the qualified type constructor of a type expression.
typeConstr :: TypeExpr -> QualIdent
typeConstr (ConstructorType   _ tc) = tc
typeConstr (ApplyType       _ ty _) = typeConstr ty
typeConstr (TupleType        _ tys) = qTupleId (length tys)
typeConstr (ListType           _ _) = qListId
typeConstr (ArrowType        _ _ _) = qArrowId
typeConstr (ParenType         _ ty) = typeConstr ty
typeConstr (VariableType       _ _) =
  error "Curry.Syntax.Utils.typeConstr: variable type"
typeConstr (ForallType       _ _ _) =
  error "Curry.Syntax.Utils.typeConstr: forall type"

-- |Return the list of variables occurring in a type expression.
typeVariables :: TypeExpr -> [Ident]
typeVariables (ConstructorType       _ _) = []
typeVariables (ApplyType       _ ty1 ty2) = typeVariables ty1 ++ typeVariables ty2
typeVariables (VariableType         _ tv) = [tv]
typeVariables (TupleType           _ tys) = concatMap typeVariables tys
typeVariables (ListType             _ ty) = typeVariables ty
typeVariables (ArrowType       _ ty1 ty2) = typeVariables ty1 ++ typeVariables ty2
typeVariables (ParenType            _ ty) = typeVariables ty
typeVariables (ForallType        _ vs ty) = vs ++ typeVariables ty

-- |Return the identifier of a variable.
varIdent :: Var a -> Ident
varIdent (Var _ v) = v

-- |Convert an infix operator into an expression
infixOp :: InfixOp a -> Expression a
infixOp (InfixOp     a op) = Variable NoSpanInfo a op
infixOp (InfixConstr a op) = Constructor NoSpanInfo a op

-- |flatten the left-hand-side to the identifier and all constructor terms
flatLhs :: Lhs a -> (Ident, [Pattern a])
flatLhs lhs = flat lhs []
  where flat (FunLhs    _ f ts) ts' = (f, ts ++ ts')
        flat (OpLhs _ t1 op t2) ts' = (op, t1 : t2 : ts')
        flat (ApLhs  _ lhs' ts) ts' = flat lhs' (ts ++ ts')

-- |Return the arity of an equation.
eqnArity :: Equation a -> Int
eqnArity (Equation _ _ lhs _) = length $ snd $ flatLhs lhs

-- |Select the label of a field
fieldLabel :: Field a -> QualIdent
fieldLabel (Field _ l _) = l

-- |Select the term of a field
fieldTerm :: Field a -> a
fieldTerm (Field _ _ t) = t

-- |Select the label and term of a field
field2Tuple :: Field a -> (QualIdent, a)
field2Tuple (Field _ l t) = (l, t)

-- |Get the operator name of an infix operator
opName :: InfixOp a -> QualIdent
opName (InfixOp     _ op) = op
opName (InfixConstr _ c ) = c

-- | Get the identifier of a constructor declaration
constrId :: ConstrDecl -> Ident
constrId (ConstrDecl  _ c  _) = c
constrId (ConOpDecl _ _ op _) = op
constrId (RecordDecl  _ c  _) = c

-- | Get the identifier of a newtype constructor declaration
nconstrId :: NewConstrDecl -> Ident
nconstrId (NewConstrDecl _ c _) = c
nconstrId (NewRecordDecl _ c _) = c

-- | Get the type of a newtype constructor declaration
nconstrType :: NewConstrDecl -> TypeExpr
nconstrType (NewConstrDecl      _ _ ty) = ty
nconstrType (NewRecordDecl _ _ (_, ty)) = ty

-- | Get record label identifiers of a constructor declaration
recordLabels :: ConstrDecl -> [Ident]
recordLabels (ConstrDecl   _ _ _) = []
recordLabels (ConOpDecl _ _ _  _) = []
recordLabels (RecordDecl  _ _ fs) = [l | FieldDecl _ ls _ <- fs, l <- ls]

-- | Get record label identifier of a newtype constructor declaration
nrecordLabels :: NewConstrDecl -> [Ident]
nrecordLabels (NewConstrDecl _ _ _     ) = []
nrecordLabels (NewRecordDecl _ _ (l, _)) = [l]

-- | Get the declared method identifiers of a type class method declaration
methods :: Decl a -> [Ident]
methods (TypeSig _ fs _) = fs
methods _                = []

-- | Get the method identifiers of a type class method implementation
impls :: Decl a -> [Ident]
impls (FunctionDecl _ _ f _) = [f]
impls _                      = []

-- | Get the declared method identifier of an interface method declaration
imethod :: IMethodDecl -> Ident
imethod (IMethodDecl _ f _ _) = f

-- | Get the arity of an interface method declaration
imethodArity :: IMethodDecl -> Maybe Int
imethodArity (IMethodDecl _ _ a _) = a

--------------------------------------------------------
-- constructing elements of the abstract syntax tree
--------------------------------------------------------

funDecl :: SpanInfo -> a -> Ident -> [Pattern a] -> Expression a -> Decl a
funDecl spi a f ts e = FunctionDecl spi a f [mkEquation spi f ts e]

mkEquation :: SpanInfo -> Ident -> [Pattern a] -> Expression a -> Equation a
mkEquation spi f ts e = 
  Equation spi Nothing (FunLhs NoSpanInfo f ts) (simpleRhs NoSpanInfo e)

simpleRhs :: SpanInfo -> Expression a -> Rhs a
simpleRhs spi e = SimpleRhs spi WhitespaceLayout e []

patDecl :: SpanInfo -> Pattern a -> Expression a -> Decl a
patDecl spi t e = PatternDecl spi t (SimpleRhs spi WhitespaceLayout e [])

varDecl :: SpanInfo -> a -> Ident -> Expression a -> Decl a
varDecl p ty = patDecl p . VariablePattern NoSpanInfo ty

constrPattern :: a -> QualIdent -> [(a, Ident)] -> Pattern a
constrPattern ty c = ConstructorPattern NoSpanInfo ty c
                   . map (uncurry (VariablePattern NoSpanInfo))

caseAlt :: SpanInfo -> Pattern a -> Expression a -> Alt a
caseAlt spi t e = Alt spi t (SimpleRhs spi WhitespaceLayout e [])

mkLet :: [Decl a] -> Expression a -> Expression a
mkLet ds e = if null ds then e else Let NoSpanInfo WhitespaceLayout ds e

mkVar :: a -> Ident -> Expression a
mkVar ty = Variable NoSpanInfo ty . qualify

mkCase :: CaseType -> Expression a -> [Alt a] -> Expression a
mkCase = Case NoSpanInfo WhitespaceLayout

mkLambda :: [Pattern a] -> Expression a -> Expression a
mkLambda = Lambda NoSpanInfo

apply :: Expression a -> [Expression a] -> Expression a
apply = foldl (Apply NoSpanInfo)

unapply :: Expression a -> [Expression a] -> (Expression a, [Expression a])
unapply (Apply _ e1 e2) es = unapply e1 (e2 : es)
unapply e               es = (e, es)

--------------------------------------------------------
-- Shorten Module
-- Module Pragmas and Equations will be removed
--------------------------------------------------------

shortenModuleAST :: Module () -> Module ()
shortenModuleAST = shortenAST

class ShortenAST a where
  shortenAST :: a -> a

instance ShortenAST (Module a) where
  shortenAST (Module spi li _ mid ex im ds) =
    Module spi li [] mid ex im (map shortenAST ds)

instance ShortenAST (Decl a) where
  shortenAST (FunctionDecl spi a idt _) =
    FunctionDecl spi a idt []
  shortenAST (ClassDecl spi li cx cls tvs fds ds) =
    ClassDecl spi li cx cls tvs fds (map shortenAST ds)
  shortenAST (InstanceDecl spi li cx cls tvs ds) =
    InstanceDecl spi li cx cls tvs (map shortenAST ds)
  shortenAST d = d
