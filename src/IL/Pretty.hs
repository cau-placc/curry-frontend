{- |
    Module      :  $Header$
    Description :  Pretty printer for IL
    Copyright   :  (c) 1999 - 2003 Wolfgang Lux
                                   Martin Engelke
                       2011 - 2015 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements just another pretty printer, this time for the
   intermediate language. It was mainly adapted from the Curry pretty
   printer which, in turn, is based on Simon Marlow's pretty printer
   for Haskell.
-}

{-# LANGUAGE CPP #-}
module IL.Pretty (ppModule) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import Curry.Base.Ident
import Curry.Base.Pretty
import IL.Type

dataIndent :: Int
dataIndent = 2

bodyIndent :: Int
bodyIndent = 2

exprIndent :: Int
exprIndent = 2

caseIndent :: Int
caseIndent = 2

altIndent :: Int
altIndent = 2

orIndent :: Int
orIndent = 2

ppModule :: Module -> Doc
ppModule (Module m is ds) = sepByBlankLine
  [ppHeader m, vcat (map ppImport is), sepByBlankLine (map ppDecl ds)]

ppHeader :: ModuleIdent -> Doc
ppHeader m = text "module" <+> text (moduleName m) <+> text "where"

ppImport :: ModuleIdent -> Doc
ppImport m = text "import" <+> text (moduleName m)

ppDecl :: Decl -> Doc
ppDecl (DataDecl                   tc n cs) = sep $
  text "data" <+> ppTypeLhs tc n :
  map (nest dataIndent)
      (zipWith (<+>) (equals : repeat (char '|')) (map ppConstr cs))
ppDecl (NewtypeDecl tc n (ConstrDecl c ty)) = sep
  [ text "newtype" <+> ppTypeLhs tc n <+> equals
  , nest dataIndent (ppConstr (ConstrDecl c [ty]))]
ppDecl (FunctionDecl             f vs ty e) = ppTypeSig f ty $$ sep
  [ ppQIdent f <+> hsep (map ppIdent vs) <+> equals
  , nest bodyIndent (ppExpr 0 e)]
ppDecl (ExternalDecl f cc ie ty) = sep
  [ text "external" <+> ppCallConv cc <+> text (show ie)
  , nest bodyIndent (ppTypeSig f ty)]
  where ppCallConv Primitive = text "primitive"
        ppCallConv CCall     = text "ccall"

ppTypeLhs :: QualIdent -> Int -> Doc
ppTypeLhs tc n = ppQIdent tc <+> hsep (map text (take n typeVars))

ppConstr :: ConstrDecl [Type] -> Doc
ppConstr (ConstrDecl c tys) = ppQIdent c <+> fsep (map (ppType 2) tys)

ppTypeSig :: QualIdent -> Type -> Doc
ppTypeSig f ty = ppQIdent f <+> text "::" <+> ppType 0 ty

ppType :: Int -> Type -> Doc
ppType p (TypeConstructor tc tys)
  | isQTupleId tc         = parens
    (fsep (punctuate comma (map (ppType 0) tys)))
  | unqualify tc == nilId = brackets (ppType 0 (head tys))
  | otherwise             = parenIf (p > 1 && not (null tys))
                            (ppQIdent tc <+> fsep (map (ppType 2) tys))
ppType _ (TypeVariable    n)
  | n >= 0    = text (typeVars !! n)
  | otherwise = text ('_':show (-n))
ppType p (TypeArrow ty1 ty2) = parenIf (p > 0)
                               (fsep (ppArrow (TypeArrow ty1 ty2)))
  where
  ppArrow (TypeArrow ty1' ty2') = ppType 1 ty1' <+> text "->" : ppArrow ty2'
  ppArrow ty                    = [ppType 0 ty]

ppBinding :: Binding -> Doc
ppBinding (Binding v expr) = sep
  [ppIdent v <+> equals, nest bodyIndent (ppExpr 0 expr)]

ppAlt :: Alt -> Doc
ppAlt (Alt pat expr) = sep
  [ppConstrTerm pat <+> text "->", nest altIndent (ppExpr 0 expr)]

ppLiteral :: Literal -> Doc
ppLiteral (Char  _ c) = text (show c)
ppLiteral (Int   _ i) = integer i
ppLiteral (Float _ f) = double f

ppConstrTerm :: ConstrTerm -> Doc
ppConstrTerm (LiteralPattern             l) = ppLiteral l
ppConstrTerm (ConstructorPattern c [v1,v2])
  | isQInfixOp c = ppIdent v1 <+> ppQInfixOp c <+> ppIdent v2
ppConstrTerm (ConstructorPattern c      vs)
  | isQTupleId c = parens $ fsep (punctuate comma $ map ppIdent vs)
  | otherwise    = ppQIdent c <+> fsep (map ppIdent vs)
ppConstrTerm (VariablePattern            v) = ppIdent v

ppExpr :: Int -> Expression -> Doc
ppExpr _ (Literal        l) = ppLiteral l
ppExpr _ (Variable       v) = ppIdent v
ppExpr _ (Function     f _) = ppQIdent f
ppExpr _ (Constructor  c _) = ppQIdent c
ppExpr p (Apply (Apply (Function   f _) e1) e2)
  | isQInfixOp f = ppInfixApp p e1 f e2
ppExpr p (Apply (Apply (Constructor c _) e1) e2)
  | isQInfixOp c = ppInfixApp p e1 c e2
ppExpr p (Apply      e1 e2) = parenIf (p > 2) $ sep
  [ppExpr 2 e1, nest exprIndent (ppExpr 3 e2)]
ppExpr p (Case _ ev e alts) = parenIf (p > 0) $
  text "case" <+> ppEval ev <+> ppExpr 0 e <+> text "of"
  $$ nest caseIndent (vcat $ map ppAlt alts)
  where ppEval Rigid = text "rigid"
        ppEval Flex  = text "flex"
ppExpr p (Or         e1 e2) = parenIf (p > 0) $ sep
  [nest orIndent (ppExpr 0 e1), char '|', nest orIndent (ppExpr 0 e2)]
ppExpr p (Exist        v e) = parenIf (p > 0) $ sep
  [text "let" <+> ppIdent v <+> text "free" <+> text "in", ppExpr 0 e]
ppExpr p (Let          b e) = parenIf (p > 0) $ sep
  [text "let" <+> ppBinding b <+> text "in",ppExpr 0 e]
ppExpr p (Letrec      bs e) = parenIf (p > 0) $ sep
  [text "letrec" <+> vcat (map ppBinding bs) <+> text "in", ppExpr 0 e]
ppExpr p (Typed       e ty) = parenIf (p > 0) $ sep
  [ppExpr 0 e, text "::", ppType 0 ty]

ppInfixApp :: Int -> Expression -> QualIdent -> Expression -> Doc
ppInfixApp p e1 op e2 = parenIf (p > 1) $ sep
  [ppExpr 2 e1 <+> ppQInfixOp op, nest exprIndent (ppExpr 2 e2)]

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
