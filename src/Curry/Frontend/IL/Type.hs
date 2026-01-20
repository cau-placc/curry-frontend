{- |
    Module      :  $Header$
    Description :  Definition of the intermediate language (IL)
    Copyright   :  (c) 1999 - 2003 Wolfgang Lux
                                   Martin Engelke
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The module 'IL' defines the intermediate language which will be
   compiled into abstract machine code. The intermediate language removes
   a lot of syntactic sugar from the Curry source language.  Top-level
   declarations are restricted to data type and function definitions. A
   newtype definition serves mainly as a hint to the backend that it must
   provide an auxiliary function for partial applications of the
   constructor (Newtype constructors must not occur in patterns
   and may be used in expressions only as partial applications.).

   Type declarations use a de-Bruijn indexing scheme (starting at 0) for
   type variables. In the type of a function, all type variables are
   numbered in the order of their occurence from left to right, i.e., a
   type '(Int -> b) -> (a,b) -> c -> (a,c)' is translated into the
   type (using integer numbers to denote the type variables)
   '(Int -> 0) -> (1,0) -> 2 -> (1,2)'.

   Pattern matching in an equation is handled via flexible and rigid
   'Case' expressions. Overlapping rules are translated with the
   help of 'Or' expressions. The intermediate language has three
   kinds of binding expressions, 'Exist' expressions introduce a
   new logical variable, 'Let' expression support a single
   non-recursive variable binding, and 'Letrec' expressions
   introduce multiple variables with recursive initializer expressions.
   The intermediate language explicitly distinguishes (local) variables
   and (global) functions in expressions.

   Note: this modified version uses haskell type 'Integer'
   instead of 'Int' for representing integer values. This provides
   an unlimited range of integer constants in Curry programs.
-}

module Curry.Frontend.IL.Type
  ( -- * Representation of (type) variables
    TypeVariableWithKind
    -- * Data types
  , Module (..), Decl (..), ConstrDecl (..), NewConstrDecl (..), Type (..)
  , Kind (..), Literal (..), ConstrTerm (..), Expression (..), Eval (..)
  , Alt (..), Binding (..)
  ) where

import Prelude hiding ((<>))

import Curry.Base.Ident
import Curry.Base.Pretty

import Curry.Frontend.Base.Expr

data Module = Module ModuleIdent [ModuleIdent] [Decl]
    deriving (Eq, Show)

data Decl
  = DataDecl         QualIdent [Kind] [ConstrDecl]
  | NewtypeDecl      QualIdent [Kind] NewConstrDecl
  | ExternalDataDecl QualIdent [Kind]
  | FunctionDecl     QualIdent [(Type, Ident)] Type Expression
  | ExternalDecl     QualIdent Int Type
    deriving (Eq, Show)

data NewConstrDecl = NewConstrDecl QualIdent Type
    deriving (Eq, Show)

data ConstrDecl = ConstrDecl QualIdent [Type]
    deriving (Eq, Show)

type TypeVariableWithKind = (Int, Kind)

data Type
  = TypeConstructor QualIdent [Type]
  | TypeVariable    Int
  | TypeArrow       Type Type
  | TypeForall      [TypeVariableWithKind] Type
    deriving (Eq, Show)

data Kind
  = KindStar
  | KindVariable Int
  | KindArrow Kind Kind
    deriving (Eq, Ord, Show)

data Literal
  = Char  Char
  | Int   Integer
  | Float Double
  | String String
    deriving (Eq, Show)

data ConstrTerm
    -- |literal patterns
  = LiteralPattern Type Literal
    -- |constructors
  | ConstructorPattern Type QualIdent [(Type, Ident)]
    -- |default
  | VariablePattern Type Ident
  deriving (Eq, Show)

data Expression
    -- |literal constants
  = Literal Type Literal
    -- |variables
  | Variable Type Ident
    -- |functions
  | Function Type QualIdent Int
    -- |constructors
  | Constructor Type QualIdent Int
    -- |applications
  | Apply Expression Expression
    -- |case expressions
  | Case Eval Expression [Alt]
    -- |non-deterministic or
  | Or Expression Expression
    -- |exist binding (introduction of a free variable)
  | Exist Ident Type Expression
    -- |let binding
  | Let Binding Expression
    -- |letrec binding
  | Letrec [Binding] Expression
    -- |typed expression
  | Typed Expression Type
  deriving (Eq, Show)

data Eval
  = Rigid
  | Flex
    deriving (Eq, Show)

data Alt = Alt ConstrTerm Expression
    deriving (Eq, Show)

data Binding = Binding Ident Expression
    deriving (Eq, Show)

instance Expr Expression where
  fv (Variable          _ v) = [v]
  fv (Apply           e1 e2) = fv e1 ++ fv e2
  fv (Case         _ e alts) = fv e  ++ fv alts
  fv (Or              e1 e2) = fv e1 ++ fv e2
  fv (Exist           v _ e) = filter (/= v) (fv e)
  fv (Let (Binding v e1) e2) = fv e1 ++ filter (/= v) (fv e2)
  fv (Letrec          bds e) = filter (`notElem` vs) (fv es ++ fv e)
    where (vs, es) = unzip [(v, e') | Binding v e' <- bds]
  fv (Typed             e _) = fv e
  fv _                       = []

instance Expr Alt where
  fv (Alt (ConstructorPattern _ _ vs) e) = filter (`notElem` map snd vs) (fv e)
  fv (Alt (VariablePattern       _ v) e) = filter (v /=) (fv e)
  fv (Alt _                           e) = fv e

instance Pretty Module where
  pPrint (Module m is ds) = sepByBlankLine
    [ppHeader m, vcat (map ppImport is), sepByBlankLine (map pPrint ds)]

ppHeader :: ModuleIdent -> Doc
ppHeader m = text "module" <+> text (moduleName m) <+> text "where"

ppImport :: ModuleIdent -> Doc
ppImport m = text "import" <+> text (moduleName m)

instance Pretty Decl where
  pPrint (DataDecl                   tc ks cs) = sep $
    text "data" <+> ppTypeLhs tc (length ks) :
    map (nest 2)
        (zipWith (<+>) (equals : repeat (char '|')) (map ppConstr cs))
  pPrint (NewtypeDecl                tc ks nc) = sep $
    text "newtype" <+> ppTypeLhs tc (length ks) :
    [nest 2 (equals <+> ppNewConstr nc)]
  pPrint (ExternalDataDecl              tc ks) =
    text "external data" <+> ppTypeLhs tc (length ks)
  pPrint (FunctionDecl             f vs ty e) = ppTypeSig f ty $$ sep
    [ ppQIdent f <+> hsep (map (ppIdent . snd) vs) <+> equals
    , nest 2 (ppExpr 0 e)]
  pPrint (ExternalDecl f _ ty) = text "external" <+> ppTypeSig f ty

ppTypeLhs :: QualIdent -> Int -> Doc
ppTypeLhs tc n = ppQIdent tc <+> hsep (map text (take n typeVars))

ppConstr :: ConstrDecl -> Doc
ppConstr (ConstrDecl c tys) = ppQIdent c <+> fsep (map (pPrintPrec 2) tys)

ppNewConstr :: NewConstrDecl -> Doc
ppNewConstr (NewConstrDecl c ty) = ppQIdent c <+> fsep [pPrintPrec 2 ty]

ppTypeSig :: QualIdent -> Type -> Doc
ppTypeSig f ty = ppQIdent f <+> text "::" <+> pPrintPrec 0 ty

instance Pretty Type where
  pPrintPrec p (TypeConstructor tc tys)
    | isQTupleId tc                    = parens
      (fsep (punctuate comma (map (pPrintPrec 0) tys)))
    | tc == qListId, [ty] <- tys       = brackets (pPrintPrec 0 ty)
    | otherwise                        = parenIf (p > 1 && not (null tys))
      (ppQIdent tc <+> fsep (map (pPrintPrec 2) tys))
  pPrintPrec _ (TypeVariable      n) = ppTypeVar n
  pPrintPrec p (TypeArrow   ty1 ty2) = parenIf (p > 0)
                                  (fsep (ppArrow (TypeArrow ty1 ty2)))
    where
    ppArrow (TypeArrow ty1' ty2') = pPrintPrec 1 ty1' <+> text "->" : ppArrow ty2'
    ppArrow ty                    = [pPrintPrec 0 ty]
  pPrintPrec p (TypeForall ns ty)
    | null ns   = pPrintPrec p ty
    | otherwise = parenIf (p > 0) $ ppQuantifiedTypeVars ns <+> pPrintPrec 0 ty

ppTypeVar :: Int -> Doc
ppTypeVar n
  | n >= 0    = text (typeVars !! n)
  | otherwise = text ('_':show (-n))

ppQuantifiedTypeVars :: [(Int, Kind)] -> Doc
ppQuantifiedTypeVars ns
  | null ns = empty
  | otherwise = text "forall" <+> hsep (map (ppTypeVar . fst) ns) <> char '.'

ppBinding :: Binding -> Doc
ppBinding (Binding v expr) = sep
  [ppIdent v <+> equals, nest 2 (ppExpr 0 expr)]

ppAlt :: Alt -> Doc
ppAlt (Alt pat expr) = sep
  [ppConstrTerm pat <+> text "->", nest 2 (ppExpr 0 expr)]

ppLiteral :: Literal -> Doc
ppLiteral (Char  c) = text (show c)
ppLiteral (Int   i) = integer i
ppLiteral (Float f) = double f
ppLiteral (String s) = text ("\"" ++ s ++ "\"")

ppConstrTerm :: ConstrTerm -> Doc
ppConstrTerm (LiteralPattern     _                    l) = ppLiteral l
ppConstrTerm (ConstructorPattern _ c [(_, v1), (_, v2)])
  | isQInfixOp c = ppIdent v1 <+> ppQInfixOp c <+> ppIdent v2
ppConstrTerm (ConstructorPattern _ c                 vs)
  | isQTupleId c = parens $ fsep (punctuate comma $ map (ppIdent . snd) vs)
  | otherwise    = ppQIdent c <+> fsep (map (ppIdent . snd) vs)
ppConstrTerm (VariablePattern    _                    v) = ppIdent v

ppExpr :: Int -> Expression -> Doc
ppExpr _ (Literal       _ l) = ppLiteral l
ppExpr _ (Variable      _ v) = ppIdent v
ppExpr _ (Function    _ f _) = ppQIdent f
ppExpr _ (Constructor _ c _) = ppQIdent c
ppExpr p (Apply (Apply (Function    _ f _) e1) e2)
  | isQInfixOp f = ppInfixApp p e1 f e2
ppExpr p (Apply (Apply (Constructor _ c _) e1) e2)
  | isQInfixOp c = ppInfixApp p e1 c e2
ppExpr p (Apply       e1 e2) = parenIf (p > 2) $ sep
  [ppExpr 2 e1, nest 2 (ppExpr 3 e2)]
ppExpr p (Case    ev e alts) = parenIf (p > 0) $
  text "case" <+> ppEval ev <+> ppExpr 0 e <+> text "of"
  $$ nest 2 (vcat $ map ppAlt alts)
  where ppEval Rigid = text "rigid"
        ppEval Flex  = text "flex"
ppExpr p (Or          e1 e2) = parenIf (p > 0) $ sep
  [nest 2 (ppExpr 0 e1), char '|', nest 2 (ppExpr 0 e2)]
ppExpr p (Exist       v _ e) = parenIf (p > 0) $ sep
  [text "let" <+> ppIdent v <+> text "free" <+> text "in", ppExpr 0 e]
ppExpr p (Let           b e) = parenIf (p > 0) $ sep
  [text "let" <+> ppBinding b <+> text "in",ppExpr 0 e]
ppExpr p (Letrec       bs e) = parenIf (p > 0) $ sep
  [text "letrec" <+> vcat (map ppBinding bs) <+> text "in", ppExpr 0 e]
ppExpr p (Typed        e ty) = parenIf (p > 0) $ sep
  [ppExpr 0 e, text "::", pPrintPrec 0 ty]

ppInfixApp :: Int -> Expression -> QualIdent -> Expression -> Doc
ppInfixApp p e1 op e2 = parenIf (p > 1) $ sep
  [ppExpr 2 e1 <+> ppQInfixOp op, nest 2 (ppExpr 2 e2)]

ppIdent :: Ident -> Doc
ppIdent ident
  | isInfixOp ident = parens (ppName ident)
  | otherwise       = ppName ident

ppQIdent :: QualIdent -> Doc
ppQIdent ident
  | isQInfixOp ident = parens (ppQual ident)
  | otherwise        = ppQual ident

ppQInfixOp :: QualIdent -> Doc
ppQInfixOp op
  | isQInfixOp op = ppQual op
  | otherwise     = char '`' <> ppQual op <> char '`'

ppName :: Ident -> Doc
ppName x = text (idName x)

ppQual :: QualIdent -> Doc
ppQual x = text (qualName x)

typeVars :: [String]
typeVars = [mkTypeVar c i | i <- [0 .. ], c <- ['a' .. 'z']] where
  mkTypeVar :: Char -> Int -> String
  mkTypeVar c i = c : if i == 0 then [] else show i
