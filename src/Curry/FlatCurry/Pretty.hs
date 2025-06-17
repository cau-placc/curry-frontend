{- |
    Module      :  $Header$
    Description :  A pretty printer for FlatCurry
    Copyright   :  (c) 2015 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements a pretty printer for FlatCurry modules.
-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Curry.FlatCurry.Pretty (pPrint, pPrintPrec) where

import Prelude hiding ((<>))
import Data.Char      (ord)

import Curry.Base.Pretty
import Curry.FlatCurry.Type

instance Pretty Prog where
  pPrint (Prog m is ts fs os) = sepByBlankLine
    [ ppHeader m ts fs
    , vcat           (map ppImport is)
    , vcat           (map pPrint   os)
    , sepByBlankLine (map pPrint   ts)
    , sepByBlankLine (map pPrint   fs)
    ]

ppHeader :: String -> [TypeDecl] -> [FuncDecl] -> Doc
ppHeader m ts fs = sep
  [text "module" <+> text m, ppExports ts fs, text "where"]

-- |pretty-print the export list
ppExports :: [TypeDecl] -> [FuncDecl] -> Doc
ppExports ts fs = parens $ list (map ppTypeExport ts ++ ppFuncExports fs)

ppTypeExport :: TypeDecl -> Doc
ppTypeExport (Type    qn vis _ cs)
  | vis == Private      = empty
  | all isPublicCons cs = ppPrefixOp qn <+> text "(..)"
  | otherwise           = ppPrefixOp qn <+> parens (list (ppConsExports cs))
    where isPublicCons (Cons _ _ v _) = v == Public
ppTypeExport (TypeNew qn vis _ nc)
  | vis == Private  = empty
  | isPublicCons nc = ppPrefixOp qn <+> text "(..)"
  | otherwise       = ppPrefixOp qn <+> parens empty
    where isPublicCons (NewCons _ v _) = v == Public
ppTypeExport (TypeSyn qn vis _ _ )
  | vis == Private = empty
  | otherwise      = ppPrefixOp qn

-- |pretty-print the export list of constructors
ppConsExports :: [ConsDecl] -> [Doc]
ppConsExports cs = [ ppPrefixOp qn | Cons qn _ Public _ <- cs]

-- |pretty-print the export list of functions
ppFuncExports :: [FuncDecl] -> [Doc]
ppFuncExports fs = [ ppPrefixOp qn | Func qn _ Public _ _ <- fs]

-- |pretty-print an import statement
ppImport :: String -> Doc
ppImport m = text "import" <+> text m

instance Pretty OpDecl where
  pPrint(Op qn fix n) = pPrint fix <+> integer n <+> ppInfixOp qn

instance Pretty Fixity where
  pPrint InfixOp  = text "infix"
  pPrint InfixlOp = text "infixl"
  pPrint InfixrOp = text "infixr"

instance Pretty TypeDecl where
  pPrint (Type    qn _ vs cs) = text "data" <+> ppQName qn
    <+> hsep (ppTVarIndex . fst <$> vs) $+$ ppConsDecls cs
  pPrint (TypeSyn qn _ vs ty) = text "type" <+> ppQName qn
    <+> hsep (ppTVarIndex . fst <$> vs) <+> equals <+> pPrintPrec 0 ty
  pPrint (TypeNew qn _ vs nc) = text "newtype" <+> ppQName qn
    <+> hsep (ppTVarIndex . fst <$> vs) <+> equals <+> pPrint nc

-- |pretty-print the constructor declarations
ppConsDecls :: [ConsDecl] -> Doc
ppConsDecls cs = indent $ vcat $
  zipWith (<+>) (equals : repeat (char '|')) (map pPrint cs)

instance Pretty ConsDecl where
  pPrint (Cons qn _ _ tys) = fsep $ ppPrefixOp qn : map (pPrintPrec 2) tys

instance Pretty NewConsDecl where
  pPrint (NewCons qn _ ty) = fsep [pPrint qn, pPrintPrec 2 ty]

instance Pretty TypeExpr where
  pPrintPrec _ (TVar           i) = ppTVarIndex i
  pPrintPrec p (FuncType ty1 ty2) = parenIf (p > 0) $ fsep
    [pPrintPrec 1 ty1, rarrow, pPrintPrec 0 ty2]
  pPrintPrec p (TCons     qn tys) = parenIf (p > 1 && not (null tys)) $ fsep
    (ppPrefixOp qn : map (pPrintPrec 2) tys)
  pPrintPrec p (ForallType vs ty)
    | null vs   = pPrintPrec p ty
    | otherwise = parenIf (p > 0) $ ppQuantifiedVars vs <+> pPrintPrec 0 ty

-- |pretty-print explicitly quantified type variables (without kinds)
ppQuantifiedVars :: [(TVarIndex, Kind)] -> Doc
ppQuantifiedVars vs
  | null vs = empty
  | otherwise = text "forall" <+> hsep (map ppTVar vs) <> char '.'

ppTVar :: (TVarIndex, Kind) -> Doc
ppTVar (i, _) = ppTVarIndex i

-- |pretty-print a type variable
ppTVarIndex :: TVarIndex -> Doc
ppTVarIndex i = text $ vars !! i
  where vars = [ if n == 0 then [c] else c : show n
               | n <- [0 :: Int ..], c <- ['a' .. 'z']
               ]

instance Pretty FuncDecl where
  pPrint (Func qn _ _ ty r)
    = hsep [ppPrefixOp qn, text "::", pPrintPrec 0 ty]
      $+$ ppPrefixOp qn <+> pPrint r

instance Pretty Rule where
  pPrint (Rule  vs e) =
    fsep (map ppVarIndex vs) <+> equals <+> indent (pPrintPrec 0 e)
  pPrint (External _) = text "external"

instance Pretty Expr where
  pPrintPrec _ (Var        v) = ppVarIndex v
  pPrintPrec _ (Lit        l) = pPrint l
  pPrintPrec p (Comb _ qn es) = ppComb p qn es
  pPrintPrec p (Free    vs e)
    | null vs             = pPrintPrec p e
    | otherwise           = parenIf (p > 0) $ sep
                            [ text "let" <+> list (map ppVarIndex vs)
                                         <+> text "free"
                            , text "in"  <+> pPrintPrec 0 e
                            ]
  pPrintPrec p (Let     ds e) = parenIf (p > 0) $
    sep [text "let" <+> ppDecls ds, text "in" <+> pPrintPrec 0 e]
  pPrintPrec p (Or     e1 e2) = parenIf (p > 0) $
    pPrintPrec 1 e1 <+> text "?" <+> pPrintPrec 1 e2
  pPrintPrec p (Case ct e bs) = parenIf (p > 0) $
    pPrint ct <+> pPrintPrec 0 e <+> text "of" $$ indent (vcat (map pPrint bs))
  pPrintPrec p (Typed   e ty) = parenIf (p > 0) $
    pPrintPrec 0 e <+> text "::" <+> pPrintPrec 0 ty

-- |pretty-print a variable
ppVarIndex :: VarIndex -> Doc
ppVarIndex i = text $ 'v' : show i

instance Pretty Literal where
  pPrint (Intc   i) = integer i
  pPrint (Floatc f) = double  f
  pPrint (Charc  c) = text (showEscape c)

-- |Escape character literal
showEscape :: Char -> String
showEscape c
  | o <   10  = "'\\00" ++ show o ++ "'"
  | o <   32  = "'\\0"  ++ show o ++ "'"
  | o == 127  = "'\\127'"
  | otherwise = show c
  where o = ord c

-- |Pretty print a constructor or function call
ppComb :: Int -> QName -> [Expr] -> Doc
ppComb _ qn []      = ppPrefixOp qn
ppComb p qn [e1,e2]
  | isInfixOp qn    = parenIf (p > 0)
                    $ hsep [pPrintPrec 1 e1, pPrint qn, pPrintPrec 1 e2]
ppComb p qn es      = parenIf (p > 0)
                    $ hsep (ppPrefixOp qn : map (pPrintPrec 1) es)

-- |pretty-print a list of declarations
ppDecls :: [(VarIndex, Expr)] -> Doc
ppDecls = vcat . map ppDecl

-- |pretty-print a single declaration
ppDecl :: (VarIndex, Expr) -> Doc
ppDecl (v, e) = ppVarIndex v <+> equals <+> pPrintPrec 0 e

instance Pretty CaseType where
  pPrint Rigid = text "case"
  pPrint Flex  = text "fcase"

instance Pretty BranchExpr where
  pPrint (Branch p e) = pPrint p <+> rarrow <+> pPrintPrec 0 e

instance Pretty Pattern where
  pPrint (Pattern c [v1,v2])
    | isInfixOp c            = ppVarIndex v1 <+> ppInfixOp c <+> ppVarIndex v2
  pPrint (Pattern  c     vs) = fsep (ppPrefixOp c : map ppVarIndex vs)
  pPrint (LPattern        l) = pPrint l

-- Names

-- |pretty-print a prefix operator
ppPrefixOp :: QName -> Doc
ppPrefixOp qn = parenIf (isInfixOp qn) (ppQName qn)

-- |pretty-print a name in infix manner
ppInfixOp :: QName -> Doc
ppInfixOp qn = if isInfixOp qn then ppQName qn else bquotes (ppQName qn)

-- |pretty-print a qualified name
ppQName :: QName -> Doc
ppQName (m, i) = text $ m ++ '.' : i

-- |Check whether an operator is an infix operator
isInfixOp :: QName -> Bool
isInfixOp = all (`elem` "~!@#$%^&*+-=<>:?./|\\") . snd

-- Indentation
indent :: Doc -> Doc
indent = nest 2
