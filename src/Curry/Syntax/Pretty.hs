{- |
    Module      :  $Header$
    Description :  A pretty printer for Curry
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements a pretty printer for Curry expressions. It was
    derived from the Haskell pretty printer provided in Simon Marlow's
    Haskell parser.
-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Curry.Syntax.Pretty
  ( pPrint, pPrintPrec, ppContext, ppInstanceType, ppIMethodImpl
  , ppIdent, ppQIdent, ppInfixOp, ppQInfixOp, ppMIdent
  ) where

import Prelude hiding ((<>))

import Curry.Base.Ident
import Curry.Base.Pretty

import Curry.Syntax.Type
import Curry.Syntax.Utils (opName)

instance Pretty (Module a) where
  pPrint (Module _ _ ps m es is ds) = ppModuleHeader ps m es is $$ ppSepBlock ds

ppModuleHeader :: [ModulePragma] -> ModuleIdent -> Maybe ExportSpec
               -> [ImportDecl] -> Doc
ppModuleHeader ps m es is
  | null is   = header
  | otherwise = header $+$ text "" $+$ vcat (map pPrint is)
  where header = vcat (map pPrint ps)
                 $+$ text "module" <+> ppMIdent m
                 <+> maybePP pPrint es <+> text "where"

instance Pretty ModulePragma where
  pPrint (LanguagePragma _      exts) =
    ppPragma "LANGUAGE" $ list $ map pPrint exts
  pPrint (OptionsPragma  _ tool args) =
    ppPragma "OPTIONS" $ maybe empty ((text "_" <>) . pPrint) tool <+> text args

ppPragma :: String -> Doc -> Doc
ppPragma kw doc = text "{-#" <+> text kw <+> doc <+> text "#-}"

instance Pretty Extension where
  pPrint (KnownExtension   _ e) = text (show e)
  pPrint (UnknownExtension _ e) = text e

instance Pretty Tool where
  pPrint (UnknownTool t) = text t
  pPrint t               = text (show t)

instance Pretty ExportSpec where
  pPrint (Exporting _ es) = parenList (map pPrint es)

instance Pretty Export where
  pPrint (Export             _ x) = ppQIdent x
  pPrint (ExportTypeWith _ tc cs) = ppQIdent tc <> parenList (map ppIdent cs)
  pPrint (ExportTypeAll     _ tc) = ppQIdent tc <> text "(..)"
  pPrint (ExportModule       _ m) = text "module" <+> ppMIdent m

instance Pretty ImportDecl where
  pPrint (ImportDecl _ m q asM is) =
    text "import" <+> ppQualified q <+> ppMIdent m <+> maybePP ppAs asM
                  <+> maybePP pPrint is
    where
      ppQualified q' = if q' then text "qualified" else empty
      ppAs m' = text "as" <+> ppMIdent m'

instance Pretty ImportSpec where
  pPrint (Importing _ is) = parenList (map pPrint is)
  pPrint (Hiding    _ is) = text "hiding" <+> parenList (map pPrint is)

instance Pretty Import where
  pPrint (Import             _ x) = ppIdent x
  pPrint (ImportTypeWith _ tc cs) = ppIdent tc <> parenList (map ppIdent cs)
  pPrint (ImportTypeAll     _ tc) = ppIdent tc <> text "(..)"

ppBlock :: Pretty a => [a] -> Doc
ppBlock = vcat . map pPrint

ppSepBlock :: Pretty a => [a] -> Doc
ppSepBlock = vcat . map (\d -> text "" $+$ pPrint d)

instance Pretty (Decl a) where
  pPrint (InfixDecl _ fix p ops) = ppPrec fix p <+> list (map ppInfixOp ops)
  pPrint (DataDecl _ tc tvs cs clss) =
    sep (ppTypeDeclLhs "data" tc tvs :
      map indent (zipWith (<+>) (equals : repeat vbar) (map pPrint cs) ++
                   [ppDeriving clss]))
  pPrint (ExternalDataDecl _ tc tvs) = ppTypeDeclLhs "external data" tc tvs
  pPrint (NewtypeDecl _ tc tvs nc clss) =
    sep (ppTypeDeclLhs "newtype" tc tvs <+> equals :
      map indent [pPrint nc, ppDeriving clss])
  pPrint (TypeDecl _ tc tvs ty) =
    sep [ppTypeDeclLhs "type" tc tvs <+> equals,indent (pPrintPrec 0 ty)]
  pPrint (TypeSig _ fs ty) =
    list (map ppIdent fs) <+> text "::" <+> pPrintPrec 0 ty
  pPrint (FunctionDecl _ _ _ eqs) = vcat (map pPrint eqs)
  pPrint (ExternalDecl   _ vs) = list (map pPrint vs) <+> text "external"
  pPrint (PatternDecl _ t rhs) = ppRule (pPrintPrec 0 t) equals rhs
  pPrint (FreeDecl       _ vs) = list (map pPrint vs) <+> text "free"
  pPrint (DefaultDecl   _ tys) =
    text "default" <+> parenList (map (pPrintPrec 0) tys)
  pPrint (ClassDecl _ _ cx cls clsvars ds) =
    ppClassInstHead "class" cx (ppIdent cls) (map ppIdent clsvars) <+>
      ppIf (not $ null ds) (text "where") $$
      ppIf (not $ null ds) (indent $ ppBlock ds)
  pPrint (InstanceDecl _ _ cx qcls inst ds) =
    ppClassInstHead "instance" cx (ppQIdent qcls) (map ppInstanceType inst) <+>
      ppIf (not $ null ds) (text "where") $$
      ppIf (not $ null ds) (indent $ ppBlock ds)

ppClassInstHead :: String -> Context -> Doc -> [Doc] -> Doc
ppClassInstHead kw cx cls tys = text kw <+> ppContext cx <+> cls <+> hsep tys

ppContext :: Context -> Doc
ppContext []  = empty
ppContext [c] = pPrint c <+> darrow
ppContext cs  = parenList (map pPrint cs) <+> darrow

instance Pretty Constraint where
  pPrint (Constraint _ qcls tys) = ppQIdent qcls <+>
    hsep (map (pPrintPrec 2) tys)

ppInstanceType :: InstanceType -> Doc
ppInstanceType = pPrintPrec 2

ppDeriving :: [QualIdent] -> Doc
ppDeriving []     = empty
ppDeriving [qcls] = text "deriving" <+> ppQIdent qcls
ppDeriving qclss  = text "deriving" <+> parenList (map ppQIdent qclss)

ppPrec :: Infix -> Maybe Precedence -> Doc
ppPrec fix p = pPrint fix <+> ppPrio p
  where
    ppPrio Nothing   = empty
    ppPrio (Just p') = integer p'

ppTypeDeclLhs :: String -> Ident -> [Ident] -> Doc
ppTypeDeclLhs kw tc tvs = text kw <+> ppIdent tc <+> hsep (map ppIdent tvs)

instance Pretty ConstrDecl where
  pPrint (ConstrDecl     _ c tys) =
    sep [ ppIdent c <+> fsep (map (pPrintPrec 2) tys) ]
  pPrint (ConOpDecl _ ty1 op ty2) =
    sep [ pPrintPrec 1 ty1, ppInfixOp op <+> pPrintPrec 1 ty2 ]
  pPrint (RecordDecl _ c fs)      =
    sep [ ppIdent c <+> record (list (map pPrint fs)) ]

instance Pretty FieldDecl where
  pPrint (FieldDecl _ ls ty) = list (map ppIdent ls)
                            <+> text "::" <+> pPrintPrec 0 ty

instance Pretty NewConstrDecl where
  pPrint (NewConstrDecl _ c ty) = sep [ppIdent c <+> pPrintPrec 2 ty]
  pPrint (NewRecordDecl _ c (i,ty)) =
    sep [ppIdent c <+> record (ppIdent i <+> text "::" <+> pPrintPrec 0 ty)]

ppQuantifiedVars :: [Ident] -> Doc
ppQuantifiedVars tvs
  | null tvs = empty
  | otherwise = text "forall" <+> hsep (map ppIdent tvs) <+> char '.'

instance Pretty (Equation a) where
  pPrint (Equation _ lhs rhs) = ppRule (pPrint lhs) equals rhs

instance Pretty (Lhs a) where
  pPrint (FunLhs   _ f ts) =
    ppIdent f <+> fsep (map (pPrintPrec 2) ts)
  pPrint (OpLhs _ t1 f t2) =
    pPrintPrec 1 t1 <+> ppInfixOp f <+> pPrintPrec 1 t2
  pPrint (ApLhs  _ lhs ts) =
    parens (pPrint lhs) <+> fsep (map (pPrintPrec 2) ts)

ppRule :: Doc -> Doc -> Rhs a -> Doc
ppRule lhs eq (SimpleRhs _ _ e ds) =
  sep [lhs <+> eq, indent (pPrintPrec 0 e)] $$ ppLocalDefs ds
ppRule lhs eq (GuardedRhs _ _ es ds) =
  sep [lhs, indent (vcat (map (ppCondExpr eq) es))] $$ ppLocalDefs ds

ppLocalDefs :: [Decl a] -> Doc
ppLocalDefs ds
  | null ds   = empty
  | otherwise = indent (text "where" <+> ppBlock ds)

-- ---------------------------------------------------------------------------
-- Interfaces
-- ---------------------------------------------------------------------------

instance Pretty Interface where
  pPrint (Interface m is ds) =
    text "interface" <+> ppMIdent m <+> text "where" <+> lbrace
      $$ vcat (punctuate semi $ map pPrint is ++ map pPrint ds)
      $$ rbrace

instance Pretty IImportDecl where
  pPrint (IImportDecl _ m) = text "import" <+> ppMIdent m

instance Pretty IDecl where
  pPrint (IInfixDecl   _ fix p op) = ppPrec fix (Just p) <+> ppQInfixOp op
  pPrint (HidingDataDecl _ tc k tvs) =
    text "hiding" <+> ppITypeDeclLhs "data" tc k tvs
  pPrint (IDataDecl   _ tc k tvs cs hs) =
    sep (ppITypeDeclLhs "data" tc k tvs :
      map indent (zipWith (<+>) (equals : repeat vbar) (map pPrint cs)) ++
      [indent (ppHiding hs)])
  pPrint (INewtypeDecl _ tc k tvs nc hs) =
    sep [ ppITypeDeclLhs "newtype" tc k tvs <+> equals
        , indent (pPrint nc)
        , indent (ppHiding hs)
        ]
  pPrint (ITypeDecl _ tc k tvs ty) =
    sep [ppITypeDeclLhs "type" tc k tvs <+> equals,indent (pPrintPrec 0 ty)]
  pPrint (IFunctionDecl _ f cm a ty) =
    sep [ ppQIdent f, maybePP (ppPragma "METHOD" . hsep . map ppIdent) cm
        , int a, text "::", pPrintPrec 0 ty ]
  pPrint (HidingClassDecl _ cx qcls k clsvars) = text "hiding" <+>
    ppClassInstHead "class" cx (ppQIdentWithKind qcls k) (map ppIdent clsvars)
  pPrint (IClassDecl _ cx qcls k clsvars ms hs) =
    ppClassInstHead "class" cx (ppQIdentWithKind qcls k) (map ppIdent clsvars)
    <+> lbrace $$
        vcat (punctuate semi $ map (indent . pPrint) ms) $$
        rbrace <+> ppHiding hs
  pPrint (IInstanceDecl _ cx qcls inst impls m) =
    ppClassInstHead "instance" cx (ppQIdent qcls) (map ppInstanceType inst) <+>
      lbrace $$
      vcat (punctuate semi $ map (indent . ppIMethodImpl) impls) $$
      rbrace <+> maybePP (ppPragma "MODULE" . ppMIdent) m

ppITypeDeclLhs :: String -> QualIdent -> Maybe KindExpr -> [Ident] -> Doc
ppITypeDeclLhs kw tc k tvs =
  text kw <+> ppQIdentWithKind tc k <+> hsep (map ppIdent tvs)

instance Pretty IMethodDecl where
  pPrint (IMethodDecl _ f a qty) =
    ppIdent f <+> maybePP int a <+> text "::" <+> pPrintPrec 0 qty

ppIMethodImpl :: IMethodImpl -> Doc
ppIMethodImpl (f, a) = ppIdent f <+> int a

ppQIdentWithKind :: QualIdent -> Maybe KindExpr -> Doc
ppQIdentWithKind tc (Just k) =
  parens $ ppQIdent tc <+> text "::" <+> pPrintPrec 0 k
ppQIdentWithKind tc Nothing  = ppQIdent tc

ppHiding :: [Ident] -> Doc
ppHiding hs
  | null hs   = empty
  | otherwise = ppPragma "HIDING" $ list $ map ppIdent hs

-- ---------------------------------------------------------------------------
-- Kinds
-- ---------------------------------------------------------------------------

instance Pretty KindExpr where
  pPrintPrec _ Star              = char '*'
  pPrintPrec _ ConstraintKind    = text "Constraint"
  pPrintPrec p (ArrowKind k1 k2) =
    parenIf (p > 0) (fsep (ppArrowKind (ArrowKind k1 k2)))
    where
      ppArrowKind (ArrowKind k1' k2') =
        pPrintPrec 1 k1' <+> rarrow : ppArrowKind k2'
      ppArrowKind k =
        [pPrintPrec 0 k]

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

instance Pretty QualTypeExpr where
  pPrint (QualTypeExpr _ cx ty) = ppContext cx <+> pPrintPrec 0 ty

instance Pretty TypeExpr where
  pPrintPrec _ (ConstructorType _ tc) = ppQIdent tc
  pPrintPrec p (ApplyType  _ ty1 ty2) = parenIf (p > 1) (ppApplyType ty1 [ty2])
     where
      ppApplyType (ApplyType _ ty1' ty2') tys =
        ppApplyType ty1' (ty2' : tys)
      ppApplyType ty                      tys =
        pPrintPrec 1 ty <+> fsep (map (pPrintPrec 2) tys)
  pPrintPrec _ (VariableType    _ tv) = ppIdent tv
  pPrintPrec _ (TupleType      _ tys) = parenList (map (pPrintPrec 0) tys)
  pPrintPrec _ (ListType        _ ty) = brackets (pPrintPrec 0 ty)
  pPrintPrec p (ArrowType  spi ty1 ty2) = parenIf (p > 0)
    (fsep (ppArrowType (ArrowType spi ty1 ty2)))
    where
      ppArrowType (ArrowType _ ty1' ty2') =
        pPrintPrec 1 ty1' <+> rarrow : ppArrowType ty2'
      ppArrowType ty                      =
        [pPrintPrec 0 ty]
  pPrintPrec _ (ParenType       _ ty) = parens (pPrintPrec 0 ty)
  pPrintPrec p (ForallType   _ vs ty)
    | null vs   = pPrintPrec p ty
    | otherwise = parenIf (p > 0) $ ppQuantifiedVars vs <+> pPrintPrec 0 ty

-- ---------------------------------------------------------------------------
-- Literals
-- ---------------------------------------------------------------------------

instance Pretty Literal where
  pPrint (Char   c) = text (show c)
  pPrint (Int    i) = integer i
  pPrint (Float  f) = double f
  pPrint (String s) = text (show s)

-- ---------------------------------------------------------------------------
-- Patterns
-- ---------------------------------------------------------------------------

instance Pretty (Pattern a) where
  pPrintPrec p (LiteralPattern _ _ l) =
    parenIf (p > 1 && isNegative l) (pPrint l)
    where
      isNegative (Char   _) = False
      isNegative (Int    i) = i < 0
      isNegative (Float  f) = f < 0.0
      isNegative (String _) = False
  pPrintPrec p (NegativePattern        _ _ l) = parenIf (p > 1)
    (ppInfixOp minusId <> pPrint l)
  pPrintPrec _ (VariablePattern        _ _ v) = ppIdent v
  pPrintPrec p (ConstructorPattern  _ _ c ts) = parenIf (p > 1 && not (null ts))
    (ppQIdent c <+> fsep (map (pPrintPrec 2) ts))
  pPrintPrec p (InfixPattern     _ _ t1 c t2) = parenIf (p > 0)
    (sep [pPrintPrec 1 t1 <+> ppQInfixOp c, indent (pPrintPrec 0 t2)])
  pPrintPrec _ (ParenPattern             _ t) = parens (pPrintPrec 0 t)
  pPrintPrec _ (TuplePattern            _ ts) =
    parenList (map (pPrintPrec 0) ts)
  pPrintPrec _ (ListPattern           _ _ ts) =
    bracketList (map (pPrintPrec 0) ts)
  pPrintPrec _ (AsPattern              _ v t) =
    ppIdent v <> char '@' <> pPrintPrec 2 t
  pPrintPrec _ (LazyPattern              _ t) = char '~' <> pPrintPrec 2 t
  pPrintPrec p (FunctionPattern     _ _ f ts) = parenIf (p > 1 && not (null ts))
    (ppQIdent f <+> fsep (map (pPrintPrec 2) ts))
  pPrintPrec p (InfixFuncPattern _ _ t1 f t2) = parenIf (p > 0)
    (sep [pPrintPrec 1 t1 <+> ppQInfixOp f, indent (pPrintPrec 0 t2)])
  pPrintPrec p (RecordPattern       _ _ c fs) = parenIf (p > 1)
    (ppQIdent c <+> record (list (map pPrint fs)))

instance Pretty a => Pretty (Field a) where
  pPrint (Field _ l t) = ppQIdent l <+> equals <+> pPrintPrec 0 t

-- ---------------------------------------------------------------------------
-- Expressions
-- ---------------------------------------------------------------------------

ppCondExpr :: Doc -> CondExpr a -> Doc
ppCondExpr eq (CondExpr _ g e) =
  vbar <+> sep [pPrintPrec 0 g <+> eq, indent (pPrintPrec 0 e)]

instance Pretty (Expression a) where
  pPrintPrec _ (Literal        _ _ l) = pPrint l
  pPrintPrec _ (Variable       _ _ v) = ppQIdent v
  pPrintPrec _ (Constructor    _ _ c) = ppQIdent c
  pPrintPrec _ (Paren            _ e) = parens (pPrintPrec 0 e)
  pPrintPrec p (Typed        _ e ty)  =
    parenIf (p > 0) (pPrintPrec 0 e <+> text "::" <+> pPrintPrec 0 ty)
  pPrintPrec _ (Tuple           _ es) = parenList (map (pPrintPrec 0) es)
  pPrintPrec _ (List          _ _ es) = bracketList (map (pPrintPrec 0) es)
  pPrintPrec _ (ListCompr     _ e qs) =
    brackets (pPrintPrec 0 e <+> vbar <+> list (map pPrint qs))
  pPrintPrec _ (EnumFrom              _ e) =
    brackets (pPrintPrec 0 e <+> text "..")
  pPrintPrec _ (EnumFromThen      _ e1 e2) =
    brackets (pPrintPrec 0 e1 <> comma <+> pPrintPrec 0 e2 <+> text "..")
  pPrintPrec _ (EnumFromTo        _ e1 e2) =
    brackets (pPrintPrec 0 e1 <+> text ".." <+> pPrintPrec 0 e2)
  pPrintPrec _ (EnumFromThenTo _ e1 e2 e3) =
    brackets (pPrintPrec 0 e1 <> comma <+> pPrintPrec 0 e2
      <+> text ".." <+> pPrintPrec 0 e3)
  pPrintPrec p (UnaryMinus          _ e) =
    parenIf (p > 1) (ppInfixOp minusId <> pPrintPrec 1 e)
  pPrintPrec p (Apply           _ e1 e2) =
    parenIf (p > 1) (sep [pPrintPrec 1 e1, indent (pPrintPrec 2 e2)])
  pPrintPrec p (InfixApply   _ e1 op e2) = parenIf (p > 0)
    (sep [pPrintPrec 1 e1 <+> ppQInfixOp (opName op), indent (pPrintPrec 1 e2)])
  pPrintPrec _ (LeftSection      _ e op) =
    parens (pPrintPrec 1 e <+> ppQInfixOp (opName op))
  pPrintPrec _ (RightSection     _ op e) =
    parens (ppQInfixOp (opName op) <+> pPrintPrec 1 e)
  pPrintPrec p (Lambda            _ t e) = parenIf (p > 0) $
    sep [backsl <> fsep (map (pPrintPrec 2) t) <+> rarrow,
         indent (pPrintPrec 0 e)]
  pPrintPrec p (Let            _ _ ds e) = parenIf (p > 0)
    (sep [text "let" <+> ppBlock ds, text "in" <+> pPrintPrec 0 e])
  pPrintPrec p (Do            _ _ sts e) = parenIf (p > 0)
    (text "do" <+> (vcat (map pPrint sts) $$ pPrintPrec 0 e))
  pPrintPrec p (IfThenElse   _ e1 e2 e3) = parenIf (p > 0)
    (text "if" <+>
     sep [pPrintPrec 0 e1,
          text "then" <+> pPrintPrec 0 e2,
          text "else" <+> pPrintPrec 0 e3])
  pPrintPrec p (Case    _ _ ct e alts) = parenIf (p > 0)
           (pPrint ct <+> pPrintPrec 0 e <+> text "of" $$
            indent (vcat (map pPrint alts)))
  pPrintPrec p (Record     _ _ c fs) = parenIf (p > 0)
    (ppQIdent c <+> record (list (map pPrint fs)))
  pPrintPrec _ (RecordUpdate _ e fs) =
    pPrintPrec 0 e <+> record (list (map pPrint fs))

instance Pretty (Statement a) where
  pPrint (StmtExpr   _ e) = pPrintPrec 0 e
  pPrint (StmtBind _ t e) =
    sep [pPrintPrec 0 t <+> larrow, indent (pPrintPrec 0 e)]
  pPrint (StmtDecl  _ _ ds) = text "let" <+> ppBlock ds

instance Pretty CaseType where
  pPrint Rigid = text "case"
  pPrint Flex  = text "fcase"

instance Pretty (Alt a) where
  pPrint (Alt _ t rhs) = ppRule (pPrintPrec 0 t) rarrow rhs

instance Pretty (Var a) where
  pPrint (Var _ ident) = ppIdent ident

instance Pretty (InfixOp a) where
  pPrint (InfixOp     _ op) = ppQInfixOp op
  pPrint (InfixConstr _ op) = ppQInfixOp op

-- ---------------------------------------------------------------------------
-- Names
-- ---------------------------------------------------------------------------

-- |Pretty print an identifier
ppIdent :: Ident -> Doc
ppIdent x = parenIf (isInfixOp x) (text (idName x))

ppQIdent :: QualIdent -> Doc
ppQIdent x = parenIf (isQInfixOp x) (text (qualName x))

ppInfixOp :: Ident -> Doc
ppInfixOp x = bquotesIf (not (isInfixOp x)) (text (idName x))

ppQInfixOp :: QualIdent -> Doc
ppQInfixOp x = bquotesIf (not (isQInfixOp x)) (text (qualName x))

ppMIdent :: ModuleIdent -> Doc
ppMIdent m = text (moduleName m)

-- ---------------------------------------------------------------------------
-- Print printing utilities
-- ---------------------------------------------------------------------------

indent :: Doc -> Doc
indent = nest 2

parenList :: [Doc] -> Doc
parenList = parens . list

record :: Doc -> Doc
record doc | isEmpty doc = braces empty
           | otherwise   = braces $ space <> doc <> space

bracketList :: [Doc] -> Doc
bracketList = brackets . list
