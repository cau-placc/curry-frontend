{- |
    Module      :  $Header$
    Copyright   :  (c) 2008        Sebastian Fischer
                       2011 - 2015 Björn Peemöller
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Transform a CurrySyntax module into a string representation without any
    pretty printing.

    Behaves like a derived Show instance even on parts with a specific one.
-}
module Curry.Syntax.ShowModule (showModule) where

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Span
import Curry.Base.SpanInfo

import Curry.Syntax.Type

-- |Show a Curry module like by an devired 'Show' instance
showModule :: Show a => Module a -> String
showModule m = showsModule m "\n"

showsModule :: Show a => Module a -> ShowS
showsModule (Module spi li ps mident espec imps decls)
  = showsString "Module "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsList (\p -> showsPragma p . newline) ps . space
  . showsModuleIdent mident . newline
  . showsMaybe showsExportSpec espec . newline
  . showsList (\i -> showsImportDecl i . newline) imps
  . showsList (\d -> showsDecl d . newline) decls

showsPragma :: ModulePragma -> ShowS
showsPragma (LanguagePragma pos exts)
  = showsString "(LanguagePragma "
  . showsSpanInfo pos . space
  . showsList showsExtension exts
  . showsString ")"
showsPragma (OptionsPragma pos mbTool args)
  = showsString "(OptionsPragma "
  . showsSpanInfo pos . space
  . showsMaybe shows mbTool
  . shows args
  . showsString ")"

showsExtension :: Extension -> ShowS
showsExtension (KnownExtension p e)
  = showsString "(KnownExtension "
  . showsSpanInfo p . space
  . shows e
  . showString ")"
showsExtension (UnknownExtension p s)
  = showsString "(UnknownExtension "
  . showsSpanInfo p . space
  . shows s
  . showString ")"

showsExportSpec :: ExportSpec -> ShowS
showsExportSpec (Exporting pos exports)
  = showsString "(Exporting "
  . showsSpanInfo pos . space
  . showsList showsExport exports
  . showsString ")"

showsExport :: Export -> ShowS
showsExport (Export spi qident)
  = showsString "(Export "
  . showsSpanInfo spi . space
  . showsQualIdent qident
  . showsString ")"
showsExport (ExportTypeWith spi qident ids)
  = showsString "(ExportTypeWith "
  . showsSpanInfo spi . space
  . showsQualIdent qident . space
  . showsList showsIdent ids
  . showsString ")"
showsExport (ExportTypeAll spi qident)
  = showsString "(ExportTypeAll "
  . showsSpanInfo spi . space
  . showsQualIdent qident
  . showsString ")"
showsExport (ExportModule spi m)
  = showsString "(ExportModule "
  . showsSpanInfo spi . space
  . showsModuleIdent m
  . showsString ")"

showsImportDecl :: ImportDecl -> ShowS
showsImportDecl (ImportDecl spi mident quali mmident mimpspec)
  = showsString "(ImportDecl "
  . showsSpanInfo spi . space
  . showsModuleIdent mident . space
  . shows quali . space
  . showsMaybe showsModuleIdent mmident . space
  . showsMaybe showsImportSpec mimpspec
  . showsString ")"

showsImportSpec :: ImportSpec -> ShowS
showsImportSpec (Importing spi imports)
  = showsString "(Importing "
  . showsSpanInfo spi . space
  . showsList showsImport imports
  . showsString ")"
showsImportSpec (Hiding spi imports)
  = showsString "(Hiding "
  . showsSpanInfo spi . space
  . showsList showsImport imports
  . showsString ")"

showsImport :: Import -> ShowS
showsImport (Import spi ident)
  = showsString "(Import "
  . showsSpanInfo spi . space
  . showsIdent ident
  . showsString ")"
showsImport (ImportTypeWith spi ident idents)
  = showsString "(ImportTypeWith "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsIdent idents
  . showsString ")"
showsImport (ImportTypeAll spi ident)
  = showsString "(ImportTypeAll "
  . showsSpanInfo spi . space
  . showsIdent ident
  . showsString ")"

showsDecl :: Show a => Decl a -> ShowS
showsDecl (InfixDecl spi infx prec idents)
  = showsString "(InfixDecl "
  . showsSpanInfo spi . space
  . shows infx . space
  . showsMaybe shows prec . space
  . showsList showsIdent idents
  . showsString ")"
showsDecl (DataDecl spi ident idents consdecls classes)
  = showsString "(DataDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsIdent idents . space
  . showsList showsConsDecl consdecls . space
  . showsList showsQualIdent classes
  . showsString ")"
showsDecl (ExternalDataDecl spi ident idents)
  = showsString "(ExternalDataDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsIdent idents
  . showsString ")"
showsDecl (NewtypeDecl spi ident idents newconsdecl classes)
  = showsString "(NewtypeDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsIdent idents . space
  . showsNewConsDecl newconsdecl . space
  . showsList showsQualIdent classes
  . showsString ")"
showsDecl (TypeDecl spi ident idents typ)
  = showsString "(TypeDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsIdent idents . space
  . showsTypeExpr typ
  . showsString ")"
showsDecl (TypeSig spi idents qtype)
  = showsString "(TypeSig "
  . showsSpanInfo spi . space
  . showsList showsIdent idents . space
  . showsQualTypeExpr qtype
  . showsString ")"
showsDecl (FunctionDecl spi a ident eqs)
  = showsString "(FunctionDecl "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsIdent ident . space
  . showsList showsEquation eqs
  . showsString ")"
showsDecl (ExternalDecl spi vars)
  = showsString "(ExternalDecl "
  . showsSpanInfo spi . space
  . showsList showsVar vars
  . showsString ")"
showsDecl (PatternDecl spi cons rhs)
  = showsString "(PatternDecl "
  . showsSpanInfo spi . space
  . showsConsTerm cons . space
  . showsRhs rhs
  . showsString ")"
showsDecl (FreeDecl spi vars)
  = showsString "(FreeDecl "
  . showsSpanInfo spi . space
  . showsList showsVar vars
  . showsString ")"
showsDecl (DefaultDecl spi types)
  = showsString "(DefaultDecl "
  . showsSpanInfo spi . space
  . showsList showsTypeExpr types
  . showsString ")"
showsDecl (ClassDecl spi li context cls clsvars funDeps decls)
  = showsString "(ClassDecl "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsContext context . space
  . showsIdent cls . space
  . showsList showsIdent clsvars . space
  . showsList showsFunDep funDeps . space
  . showsList showsDecl decls
  . showsString ")"
showsDecl (InstanceDecl spi li context qcls inst decls)
  = showsString "(InstanceDecl "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsContext context . space
  . showsQualIdent qcls . space
  . showsList showsInstanceType inst . space
  . showsList showsDecl decls
  . showsString ")"

showsContext :: Context -> ShowS
showsContext = showsList showsConstraint

showsConstraint :: Constraint -> ShowS
showsConstraint (Constraint spi qcls tys)
  = showsString "(Constraint "
  . showsSpanInfo spi . space
  . showsQualIdent qcls . space
  . showsList showsTypeExpr tys
  . showsString ")"

showsInstanceType :: InstanceType -> ShowS
showsInstanceType = showsTypeExpr

showsFunDep :: FunDep -> ShowS
showsFunDep (FunDep spi ltvs rtvs)
  = showsString "(FunDep "
  . showsSpanInfo spi . space
  . showsList showsIdent ltvs . space
  . showsList showsIdent rtvs
  . showsString ")"

showsConsDecl :: ConstrDecl -> ShowS
showsConsDecl (ConstrDecl spi ident types)
  = showsString "(ConstrDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsTypeExpr types
  . showsString ")"
showsConsDecl (ConOpDecl spi ty1 ident ty2)
  = showsString "(ConOpDecl "
  . showsSpanInfo spi . space
  . showsTypeExpr ty1 . space
  . showsIdent ident . space
  . showsTypeExpr ty2
  . showsString ")"
showsConsDecl (RecordDecl spi ident fs)
  = showsString "(RecordDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsFieldDecl fs
  . showsString ")"

showsFieldDecl :: FieldDecl -> ShowS
showsFieldDecl (FieldDecl spi labels ty)
  = showsString "(FieldDecl "
  . showsSpanInfo spi . space
  . showsList showsIdent labels . space
  . showsTypeExpr ty
  . showsString ")"

showsNewConsDecl :: NewConstrDecl -> ShowS
showsNewConsDecl (NewConstrDecl spi ident typ)
  = showsString "(NewConstrDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsTypeExpr typ
  . showsString ")"
showsNewConsDecl (NewRecordDecl spi ident fld)
  = showsString "(NewRecordDecl "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsPair showsIdent showsTypeExpr fld
  . showsString ")"

showsQualTypeExpr :: QualTypeExpr -> ShowS
showsQualTypeExpr (QualTypeExpr spi context typ)
  = showsString "(QualTypeExpr "
  . showsSpanInfo spi . space
  . showsContext context . space
  . showsTypeExpr typ
  . showsString ")"

showsTypeExpr :: TypeExpr -> ShowS
showsTypeExpr (ConstructorType spi qident)
  = showsString "(ConstructorType "
  . showsSpanInfo spi . space
  . showsQualIdent qident . space
  . showsString ")"
showsTypeExpr (ApplyType spi type1 type2)
  = showsString "(ApplyType "
  . showsSpanInfo spi . space
  . showsTypeExpr type1 . space
  . showsTypeExpr type2 . space
  . showsString ")"
showsTypeExpr (VariableType spi ident)
  = showsString "(VariableType "
  . showsSpanInfo spi . space
  . showsIdent ident
  . showsString ")"
showsTypeExpr (TupleType spi types)
  = showsString "(TupleType "
  . showsSpanInfo spi . space
  . showsList showsTypeExpr types
  . showsString ")"
showsTypeExpr (ListType spi typ)
  = showsString "(ListType "
  . showsSpanInfo spi . space
  . showsTypeExpr typ
  . showsString ")"
showsTypeExpr (ArrowType spi dom ran)
  = showsString "(ArrowType "
  . showsSpanInfo spi . space
  . showsTypeExpr dom . space
  . showsTypeExpr ran
  . showsString ")"
showsTypeExpr (ParenType spi ty)
  = showsString "(ParenType "
  . showsSpanInfo spi . space
  . showsTypeExpr ty
  . showsString ")"
showsTypeExpr (ForallType spi vars ty)
  = showsString "(ForallType "
  . showsSpanInfo spi . space
  . showsList showsIdent vars
  . showsTypeExpr ty
  . showsString ")"

showsEquation :: Show a => Equation a -> ShowS
showsEquation (Equation spi a lhs rhs)
  = showsString "(Equation "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsLhs lhs . space
  . showsRhs rhs
  . showsString ")"

showsLhs :: Show a => Lhs a -> ShowS
showsLhs (FunLhs spi ident conss)
  = showsString "(FunLhs "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsList showsConsTerm conss
  . showsString ")"
showsLhs (OpLhs spi cons1 ident cons2)
  = showsString "(OpLhs "
  . showsSpanInfo spi . space
  . showsConsTerm cons1 . space
  . showsIdent ident . space
  . showsConsTerm cons2
  . showsString ")"
showsLhs (ApLhs spi lhs conss)
  = showsString "(ApLhs "
  . showsSpanInfo spi . space
  . showsLhs lhs . space
  . showsList showsConsTerm conss
  . showsString ")"

showsRhs :: Show a => Rhs a -> ShowS
showsRhs (SimpleRhs spi li expr decls)
  = showsString "(SimpleRhs "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsExpression expr . space
  . showsList showsDecl decls
  . showsString ")"
showsRhs (GuardedRhs spi li cexps decls)
  = showsString "(GuardedRhs "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsList showsCondExpr cexps . space
  . showsList showsDecl decls
  . showsString ")"

showsCondExpr :: Show a => CondExpr a -> ShowS
showsCondExpr (CondExpr spi exp1 exp2)
  = showsString "(CondExpr "
  . showsSpanInfo spi . space
  . showsExpression exp1 . space
  . showsExpression exp2
  . showsString ")"

showsLiteral :: Literal -> ShowS
showsLiteral (Char c)
  = showsString "(Char "
  . shows c
  . showsString ")"
showsLiteral (Int n)
  = showsString "(Int "
  . shows n
  . showsString ")"
showsLiteral (Float x)
  = showsString "(Float "
  . shows x
  . showsString ")"
showsLiteral (String s)
  = showsString "(String "
  . shows s
  . showsString ")"

showsConsTerm :: Show a => Pattern a -> ShowS
showsConsTerm (LiteralPattern spi a lit)
  = showsString "(LiteralPattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsLiteral lit
  . showsString ")"
showsConsTerm (NegativePattern spi a lit)
  = showsString "(NegativePattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsLiteral lit
  . showsString ")"
showsConsTerm (VariablePattern spi a ident)
  = showsString "(VariablePattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsIdent ident
  . showsString ")"
showsConsTerm (ConstructorPattern spi a qident conss)
  = showsString "(ConstructorPattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsQualIdent qident . space
  . showsList showsConsTerm conss
  . showsString ")"
showsConsTerm (InfixPattern spi a cons1 qident cons2)
  = showsString "(InfixPattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsConsTerm cons1 . space
  . showsQualIdent qident . space
  . showsConsTerm cons2
  . showsString ")"
showsConsTerm (ParenPattern spi cons)
  = showsString "(ParenPattern "
  . showsSpanInfo spi . space
  . showsConsTerm cons
  . showsString ")"
showsConsTerm (TuplePattern spi conss)
  = showsString "(TuplePattern "
  . showsSpanInfo spi . space
  . showsList showsConsTerm conss
  . showsString ")"
showsConsTerm (ListPattern spi a conss)
  = showsString "(ListPattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsList showsConsTerm conss
  . showsString ")"
showsConsTerm (AsPattern spi ident cons)
  = showsString "(AsPattern "
  . showsSpanInfo spi . space
  . showsIdent ident . space
  . showsConsTerm cons
  . showsString ")"
showsConsTerm (LazyPattern spi cons)
  = showsString "(LazyPattern "
  . showsSpanInfo spi . space
  . showsConsTerm cons
  . showsString ")"
showsConsTerm (FunctionPattern spi a qident conss)
  = showsString "(FunctionPattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsQualIdent qident . space
  . showsList showsConsTerm conss
  . showsString ")"
showsConsTerm (InfixFuncPattern spi a cons1 qident cons2)
  = showsString "(InfixFuncPattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsConsTerm cons1 . space
  . showsQualIdent qident . space
  . showsConsTerm cons2
  . showsString ")"
showsConsTerm (RecordPattern spi a qident cfields)
  = showsString "(RecordPattern "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsQualIdent qident . space
  . showsList (showsField showsConsTerm) cfields . space
  . showsString ")"

showsExpression :: Show a => Expression a -> ShowS
showsExpression (Literal spi a lit)
  = showsString "(Literal "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsLiteral lit
  . showsString ")"
showsExpression (Variable spi a qident)
  = showsString "(Variable "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsQualIdent qident
  . showsString ")"
showsExpression (Constructor spi a qident)
  = showsString "(Constructor "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsQualIdent qident
  . showsString ")"
showsExpression (Paren spi expr)
  = showsString "(Paren "
  . showsSpanInfo spi . space
  . showsExpression expr
  . showsString ")"
showsExpression (Typed spi expr qtype)
  = showsString "(Typed "
  . showsSpanInfo spi . space
  . showsExpression expr . space
  . showsQualTypeExpr qtype
  . showsString ")"
showsExpression (Tuple spi exps)
  = showsString "(Tuple "
  . showsSpanInfo spi . space
  . showsList showsExpression exps
  . showsString ")"
showsExpression (List spi a exps)
  = showsString "(List "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsList showsExpression exps
  . showsString ")"
showsExpression (ListCompr spi expr stmts)
  = showsString "(ListCompr "
  . showsSpanInfo spi . space
  . showsExpression expr . space
  . showsList showsStatement stmts
  . showsString ")"
showsExpression (EnumFrom spi expr)
  = showsString "(EnumFrom "
  . showsSpanInfo spi . space
  . showsExpression expr
  . showsString ")"
showsExpression (EnumFromThen spi exp1 exp2)
  = showsString "(EnumFromThen "
  . showsSpanInfo spi . space
  . showsExpression exp1 . space
  . showsExpression exp2
  . showsString ")"
showsExpression (EnumFromTo spi exp1 exp2)
  = showsString "(EnumFromTo "
  . showsSpanInfo spi . space
  . showsExpression exp1 . space
  . showsExpression exp2
  . showsString ")"
showsExpression (EnumFromThenTo spi exp1 exp2 exp3)
  = showsString "(EnumFromThenTo "
  . showsSpanInfo spi . space
  . showsExpression exp1 . space
  . showsExpression exp2 . space
  . showsExpression exp3
  . showsString ")"
showsExpression (UnaryMinus spi expr)
  = showsString "(UnaryMinus "
  . showsSpanInfo spi . space
  . showsExpression expr
  . showsString ")"
showsExpression (Apply spi exp1 exp2)
  = showsString "(Apply "
  . showsSpanInfo spi . space
  . showsExpression exp1 . space
  . showsExpression exp2
  . showsString ")"
showsExpression (InfixApply spi exp1 op exp2)
  = showsString "(InfixApply "
  . showsSpanInfo spi . space
  . showsExpression exp1 . space
  . showsInfixOp op . space
  . showsExpression exp2
  . showsString ")"
showsExpression (LeftSection spi expr op)
  = showsString "(LeftSection "
  . showsSpanInfo spi . space
  . showsExpression expr . space
  . showsInfixOp op
  . showsString ")"
showsExpression (RightSection spi op expr)
  = showsString "(RightSection "
  . showsSpanInfo spi . space
  . showsInfixOp op . space
  . showsExpression expr
  . showsString ")"
showsExpression (Lambda spi conss expr)
  = showsString "(Lambda "
  . showsSpanInfo spi . space
  . showsList showsConsTerm conss . space
  . showsExpression expr
  . showsString ")"
showsExpression (Let spi li decls expr)
  = showsString "(Let "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsList showsDecl decls . space
  . showsExpression expr
  . showsString ")"
showsExpression (Do spi li stmts expr)
  = showsString "(Do "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsList showsStatement stmts . space
  . showsExpression expr
  . showsString ")"
showsExpression (IfThenElse spi exp1 exp2 exp3)
  = showsString "(IfThenElse "
  . showsSpanInfo spi . space
  . showsExpression exp1 . space
  . showsExpression exp2 . space
  . showsExpression exp3
  . showsString ")"
showsExpression (Case spi li ct expr alts)
  = showsString "(Case "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsCaseType ct . space
  . showsExpression expr . space
  . showsList showsAlt alts
  . showsString ")"
showsExpression (RecordUpdate spi expr efields)
  = showsString "(RecordUpdate "
  . showsSpanInfo spi . space
  . showsExpression expr . space
  . showsList (showsField showsExpression) efields
  . showsString ")"
showsExpression (Record spi a qident efields)
  = showsString "(Record "
  . showsSpanInfo spi . space
  . showsPrec 11 a . space
  . showsQualIdent qident . space
  . showsList (showsField showsExpression) efields
  . showsString ")"

showsInfixOp :: Show a => InfixOp a -> ShowS
showsInfixOp (InfixOp a qident)
  = showsString "(InfixOp "
  . showsPrec 11 a . space
  . showsQualIdent qident
  . showsString ")"
showsInfixOp (InfixConstr a qident)
  = showsString "(InfixConstr "
  . showsPrec 11 a . space
  . showsQualIdent qident
  . showsString ")"

showsStatement :: Show a => Statement a -> ShowS
showsStatement (StmtExpr spi expr)
  = showsString "(StmtExpr "
  . showsSpanInfo spi . space
  . showsExpression expr
  . showsString ")"
showsStatement (StmtDecl spi li decls)
  = showsString "(StmtDecl "
  . showsSpanInfo spi . space
  . showsLayoutInfo li . space
  . showsList showsDecl decls
  . showsString ")"
showsStatement (StmtBind spi cons expr)
  = showsString "(StmtBind "
  . showsSpanInfo spi . space
  . showsConsTerm cons . space
  . showsExpression expr
  . showsString ")"

showsCaseType :: CaseType -> ShowS
showsCaseType Rigid = showsString "Rigid"
showsCaseType Flex  = showsString "Flex"

showsAlt :: Show a => Alt a -> ShowS
showsAlt (Alt spi cons rhs)
  = showsString "(Alt "
  . showsSpanInfo spi . space
  . showsConsTerm cons . space
  . showsRhs rhs
  . showsString ")"

showsField :: (a -> ShowS) -> Field a -> ShowS
showsField sa (Field spi ident a)
  = showsString "(Field "
  . showsSpanInfo spi . space
  . showsQualIdent ident . space
  . sa a
  . showsString ")"

showsVar :: Show a => Var a -> ShowS
showsVar (Var a ident)
  = showsString "(Var "
  . showsPrec 11 a . space
  . showsIdent ident
  . showsString ")"

showsPosition :: Position -> ShowS
showsPosition NoPos = showsString "NoPos"
showsPosition Position { line = l, column = c }
   = showsString "(Position "
   . shows l . space
   . shows c
   . showsString ")"

showsSpanInfo :: SpanInfo -> ShowS
showsSpanInfo NoSpanInfo = showsString "NoSpanInfo"
showsSpanInfo SpanInfo { srcSpan = sp, srcInfoPoints = ss }
  = showsString "(SpanInfo "
  . showsSpan sp . space
  . showsList showsSpan ss
  . showsString ")"

showsLayoutInfo :: LayoutInfo -> ShowS
showsLayoutInfo WhitespaceLayout = showsString "WhitespaceLayout"
showsLayoutInfo (ExplicitLayout ss)
  = showsString "(ExplicitLayout "
  . showsList showsSpan ss
  . showsString ")"

showsSpan :: Span -> ShowS
showsSpan NoSpan = showsString "NoSpan"
showsSpan Span { start = s, end = e }
  = showsString "(Span "
  . showsPosition s . space
  . showsPosition e
  . showsString ")"

showsString :: String -> ShowS
showsString = (++)

space :: ShowS
space = showsString " "

newline :: ShowS
newline = showsString "\n"

showsMaybe :: (a -> ShowS) -> Maybe a -> ShowS
showsMaybe shs = maybe (showsString "Nothing")
                       (\x -> showsString "(Just " . shs x . showsString ")")

showsList :: (a -> ShowS) -> [a] -> ShowS
showsList _   [] = showsString "[]"
showsList shs (x:xs)
  = showsString "["
  . foldl (\sys y -> sys . showsString "," . shs y) (shs x) xs
  . showsString "]"

showsPair :: (a -> ShowS) -> (b -> ShowS) -> (a,b) -> ShowS
showsPair sa sb (a,b)
  = showsString "(" . sa a . showsString "," . sb b . showsString ")"

showsIdent :: Ident -> ShowS
showsIdent (Ident spi x n)
  = showsString "(Ident " . showsSpanInfo spi . space
  . shows x . space . shows n . showsString ")"

showsQualIdent :: QualIdent -> ShowS
showsQualIdent (QualIdent spi mident ident)
  = showsString "(QualIdent "
  . showsSpanInfo spi . space
  . showsMaybe showsModuleIdent mident
  . space
  . showsIdent ident
  . showsString ")"

showsModuleIdent :: ModuleIdent -> ShowS
showsModuleIdent (ModuleIdent spi ss)
  = showsString "(ModuleIdent "
  . showsSpanInfo spi . space
  . showsList (showsQuotes showsString) ss
  . showsString ")"

showsQuotes :: (a -> ShowS) -> a -> ShowS
showsQuotes sa a
  = showsString "\"" . sa a . showsString "\""
