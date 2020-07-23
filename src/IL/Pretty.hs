{- |
    Module      :  $Header$
    Description :  Pretty printer for IL
    Copyright   :  (c) 1999 - 2003 Wolfgang Lux
                                   Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2017        Finn Teegen
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
ppDecl (NewtypeDecl                tc n nc) = sep $
  text "newtype" <+> ppTypeLhs tc n :
  [nest dataIndent (equals <+> ppNewConstr nc)]
ppDecl (ExternalDataDecl              tc n) =
  text "external data" <+> ppTypeLhs tc n
ppDecl (FunctionDecl             f vs ty e) = ppTypeSig f ty $$ sep
  [ ppQIdent f <+> hsep (map (ppIdent . snd) vs) <+> equals
  , nest bodyIndent (ppExpr 0 e)]
ppDecl (ExternalDecl f ty) = text "external" <+> ppTypeSig f ty

ppTypeLhs :: QualIdent -> Int -> Doc
ppTypeLhs tc n = ppQIdent tc <+> hsep (map text (take n typeVars))

ppConstr :: ConstrDecl -> Doc
ppConstr (ConstrDecl c tys) = ppQIdent c <+> fsep (map (ppType 2) tys)

ppNewConstr :: NewConstrDecl -> Doc
ppNewConstr (NewConstrDecl c ty) = ppQIdent c <+> fsep [ppType 2 ty]

ppTypeSig :: QualIdent -> Type -> Doc
ppTypeSig f ty = ppQIdent f <+> text "::" <+> ppType 0 ty

ppType :: Int -> Type -> Doc
ppType p (TypeConstructor tc tys)
  | isQTupleId tc                    = parens
    (fsep (punctuate comma (map (ppType 0) tys)))
  | tc == qListId && length tys == 1 = brackets (ppType 0 (head tys))
  | otherwise                        = parenIf (p > 1 && not (null tys))
    (ppQIdent tc <+> fsep (map (ppType 2) tys))
ppType _ (TypeVariable    n) = ppTypeVar n
ppType p (TypeArrow ty1 ty2) = parenIf (p > 0)
                               (fsep (ppArrow (TypeArrow ty1 ty2)))
  where
  ppArrow (TypeArrow ty1' ty2') = ppType 1 ty1' <+> text "->" : ppArrow ty2'
  ppArrow ty                    = [ppType 0 ty]
ppType p (TypeForall ns ty)
  | null ns   = ppType p ty
  | otherwise = parenIf (p > 0) $ ppQuantifiedTypeVars ns <+> ppType 0 ty

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
  [ppIdent v <+> equals, nest bodyIndent (ppExpr 0 expr)]

ppAlt :: Alt -> Doc
ppAlt (Alt pat expr) = sep
  [ppConstrTerm pat <+> text "->", nest altIndent (ppExpr 0 expr)]

ppLiteral :: Literal -> Doc
ppLiteral (Char  c) = text (show c)
ppLiteral (Int   i) = integer i
ppLiteral (Float f) = double f

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
  [ppExpr 2 e1, nest exprIndent (ppExpr 3 e2)]
ppExpr p (Case    ev e alts) = parenIf (p > 0) $
  text "case" <+> ppEval ev <+> ppExpr 0 e <+> text "of"
  $$ nest caseIndent (vcat $ map ppAlt alts)
  where ppEval Rigid = text "rigid"
        ppEval Flex  = text "flex"
ppExpr p (Or          e1 e2) = parenIf (p > 0) $ sep
  [nest orIndent (ppExpr 0 e1), char '|', nest orIndent (ppExpr 0 e2)]
ppExpr p (Exist       v _ e) = parenIf (p > 0) $ sep
  [text "let" <+> ppIdent v <+> text "free" <+> text "in", ppExpr 0 e]
ppExpr p (Let           b e) = parenIf (p > 0) $ sep
  [text "let" <+> ppBinding b <+> text "in",ppExpr 0 e]
ppExpr p (Letrec       bs e) = parenIf (p > 0) $ sep
  [text "letrec" <+> vcat (map ppBinding bs) <+> text "in", ppExpr 0 e]
ppExpr p (Typed        e ty) = parenIf (p > 0) $ sep
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
