{- |
    Module      :  $Header$
    Description :  A Parser for Curry
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The Curry parser is implemented using the (mostly) LL(1) parsing
    combinators implemented in 'Curry.Base.LLParseComb'.
-}
module Curry.Syntax.Parser
  ( parseSource, parseHeader, parsePragmas, parseInterface, parseGoal
  ) where

import Curry.Base.Ident
import Curry.Base.Monad       (CYM)
import Curry.Base.Position    (Position(..), getPosition, setPosition, incr)
import Curry.Base.LLParseComb
import Curry.Base.Span        hiding (file) -- clash with Position.file
import Curry.Base.SpanInfo

import Curry.Syntax.Extension
import Curry.Syntax.Lexer (Token (..), Category (..), Attributes (..), lexer)
import Curry.Syntax.Type

-- |Parse a 'Module'
parseSource :: FilePath -> String -> CYM (Module ())
parseSource = fullParser (mkMod <$> moduleHeader <*> layout moduleDecls) lexer
  where mkMod f ((im, ds), lay) = f lay im ds

-- |Parse only pragmas of a 'Module'
parsePragmas :: FilePath -> String -> CYM (Module ())
parsePragmas
  = prefixParser ((\ps sp -> setEndPosition NoPos
                              (Module (spanInfo sp []) WhitespaceLayout
                                 ps mainMIdent Nothing [] []))
                    <$> modulePragmas <*> spanPosition)
      lexer

-- |Parse a 'Module' header
parseHeader :: FilePath -> String -> CYM (Module ())
parseHeader = prefixParser
  (mkMod <$> moduleHeader <*> startLayout importDecls) lexer
  where
    importDecls = mkImport <$> many ((,) <$> importDecl
                                         <*> many (spanPosition <*-> semicolon))
    mkImport xs = let (im, spss) = unzip xs in (im, concat spss)
    mkMod f (im, lay) = f lay im []

-- |Parse an 'Interface'
parseInterface :: FilePath -> String -> CYM Interface
parseInterface = fullParser interface lexer

-- |Parse a 'Goal'
parseGoal :: String -> CYM (Goal ())
parseGoal = fullParser goal lexer ""

-- ---------------------------------------------------------------------------
-- Module header
-- ---------------------------------------------------------------------------

-- |Parser for a module header
moduleHeader :: Parser a Token
                  (LayoutInfo -> [ImportDecl] -> [Decl b] -> Module b)
moduleHeader =
  (\sp ps (m, es, inf) lay is ds -> updateEndPos $
      Module (spanInfo sp inf) lay ps m es is ds)
    <$> spanPosition
    <*> modulePragmas
    <*> header
  where header = (\sp1 m es sp2 -> (m, es, [sp1,sp2]))
                    <$>  tokenSpan KW_module
                    <*>  modIdent
                    <*>  option exportSpec
                    <*>  spanPosition
                    <*-> expectWhere
                `opt` (mainMIdent, Nothing, [])

modulePragmas :: Parser a Token [ModulePragma]
modulePragmas = many (languagePragma <|> optionsPragma)

languagePragma :: Parser a Token ModulePragma
languagePragma =   languagePragma'
              <$>  tokenSpan PragmaLanguage
              <*>  (languageExtension `sepBy1Sp` comma)
              <*>  tokenSpan PragmaEnd
  where languageExtension = classifyExtension <$> ident
        languagePragma' sp1 (ex, ss) sp2 = updateEndPos $
          LanguagePragma (spanInfo sp1 (sp1 : ss ++ [sp2])) ex

-- TODO The span info is not 100% complete due to the lexer
-- combining OPTIONS, toolVal and toolArgs
optionsPragma :: Parser a Token ModulePragma
optionsPragma = optionsPragma'
           <$>  spanPosition
           <*>  token PragmaOptions
           <*>  tokenSpan PragmaEnd
  where optionsPragma' sp1 a sp2 = updateEndPos $
          OptionsPragma (spanInfo sp1 [sp1, sp2])
                        (classifyTool <$> toolVal a)
                        (toolArgs a)

-- |Parser for an export specification
exportSpec :: Parser a Token ExportSpec
exportSpec = exportSpec' <$> spanPosition <*> parensSp (export `sepBySp` comma)
  where exportSpec' sp1 ((ex, ss),sp2,sp3) = updateEndPos $
          Exporting (spanInfo sp1 (sp2:(ss ++ [sp3]))) ex

-- |Parser for an export item
export :: Parser a Token Export
export =  qtycon <**> (tcExportWith <$> parensSp spec `opt` tcExport)
      <|> tcExport <$> qfun <\> qtycon
      <|> exportModule' <$> tokenSpan KW_module <*> modIdent
  where spec =  (\sp      -> (ExportTypeAll    , [sp])) <$> tokenSpan DotDot
            <|> (\(c, ss) -> (exportTypeWith' c,  ss )) <$> con `sepBySp` comma
        tcExport qtc = updateEndPos $ Export (fromSrcSpan (getSrcSpan qtc)) qtc
        tcExportWith ((spc, ss), sp1, sp2) qtc =
          updateEndPos $ setSrcInfoPoints (sp1 : (ss ++ [sp2])) $
          spc (fromSrcSpan (getSrcSpan qtc)) qtc
        exportTypeWith' c spi qtc = ExportTypeWith spi qtc c
        exportModule' sp = updateEndPos . ExportModule (spanInfo sp [sp])

moduleDecls :: Parser a Token (([ImportDecl], [Decl ()]), [Span])
moduleDecls = mkImpDecl <$> importDecl
                        <*> (moduleDecls' `opt` ([], [], []))
          <|> mkTopDecl <$> topDecls
  where
    mkImpDecl i (is, ds, sps) = ((i:is, ds), sps)
    mkTopDecl (ds, sps) = (([], ds), sps)

    moduleDecls' = mkDecls <$> spanPosition <*-> semicolon <*> moduleDecls
    mkDecls sp ((im, ds), sps) = (im, ds, sp:sps)

-- |Parser for a single import declaration
importDecl :: Parser a Token ImportDecl
importDecl =  importDecl'
          <$> tokenSpan KW_import
          <*> option (tokenSpan Id_qualified)
          <*> modIdent
          <*> option ((,) <$> tokenSpan Id_as <*> modIdent)
          <*> option importSpec
  where
    importDecl' sp1 (Just sp2) mid (Just (sp3, alias)) = updateEndPos .
      ImportDecl (spanInfo sp1 [sp1, sp2, sp3]) mid True  (Just alias)
    importDecl' sp1 Nothing    mid (Just (sp3, alias)) = updateEndPos .
      ImportDecl (spanInfo sp1      [sp1, sp3]) mid False (Just alias)
    importDecl' sp1 (Just sp2) mid Nothing             = updateEndPos .
      ImportDecl (spanInfo sp1      [sp1, sp2]) mid True  Nothing
    importDecl' sp1 Nothing    mid Nothing             = updateEndPos .
      ImportDecl (spanInfo sp1           [sp1]) mid False Nothing

-- |Parser for an import specification
importSpec :: Parser a Token ImportSpec
importSpec =   spanPosition
          <**> (hiding' <$-> token Id_hiding `opt` importing')
          <*>  parensSp (importSp `sepBySp` comma)
  where
    hiding' sp1 ((specs, ss), sp2, sp3) = updateEndPos $
      Hiding    (spanInfo sp1 (sp1 : sp2 : (ss ++ [sp3]))) specs
    importing' sp1 ((specs, ss), sp2, sp3) = updateEndPos $
      Importing (spanInfo sp1 (      sp2 : (ss ++ [sp3]))) specs

importSp :: Parser a Token Import
importSp = tycon <**> (tcImportWith <$> parensSp spec `opt` tcImport)
      <|> tcImport <$> fun <\> tycon
  where spec =  (\sp      -> (ImportTypeAll    , [sp])) <$> tokenSpan DotDot
            <|> (\(c, ss) -> (importTypeWith' c,  ss )) <$> con `sepBySp` comma
        tcImport tc = updateEndPos $ Import (fromSrcSpan (getSrcSpan tc)) tc
        tcImportWith ((spc, ss), sp1, sp2) tc =
          updateEndPos $ setSrcInfoPoints (sp1 : (ss ++ [sp2])) $
          spc (fromSrcSpan (getSrcSpan tc)) tc
        importTypeWith' c spi tc = ImportTypeWith spi tc c
-- ---------------------------------------------------------------------------
-- Interfaces
-- ---------------------------------------------------------------------------

-- |Parser for an interface
interface :: Parser a Token Interface
interface = uncurry <$> intfHeader <*> braces intfDecls

intfHeader :: Parser a Token ([IImportDecl] -> [IDecl] -> Interface)
intfHeader = Interface <$-> token Id_interface <*> modIdent <*-> expectWhere

intfDecls :: Parser a Token ([IImportDecl], [IDecl])
intfDecls = impDecl <$> iImportDecl
                    <*> (semicolon <-*> intfDecls `opt` ([], []))
        <|> (,) [] <$> intfDecl `sepBy` semicolon
  where impDecl i (is, ds) = (i:is, ds)

-- |Parser for a single interface import declaration
iImportDecl :: Parser a Token IImportDecl
iImportDecl = IImportDecl <$> tokenPos KW_import <*> modIdent

-- |Parser for a single interface declaration
intfDecl :: Parser a Token IDecl
intfDecl = choice [ iInfixDecl, iHidingDecl, iDataDecl, iNewtypeDecl
                  , iTypeDecl , iFunctionDecl <\> token Id_hiding
                  , iClassDecl, iInstanceDecl ]

-- |Parser for an interface infix declaration
iInfixDecl :: Parser a Token IDecl
iInfixDecl = infixDeclLhs iInfixDecl' <*> integer <*> qfunop
  where iInfixDecl' sp = IInfixDecl (span2Pos sp)

-- |Parser for an interface hiding declaration
iHidingDecl :: Parser a Token IDecl
iHidingDecl = tokenPos Id_hiding <**> (hDataDecl <|> hClassDecl)
  where
  hDataDecl = hiddenData <$-> token KW_data <*> withKind qtycon <*> many tyvar
  hClassDecl = hiddenClass <$> classInstHead KW_class (withKind qtycls) clsvar
                           <*-> token KW_where <*> braces (fun `sepBy` semicolon)
  hiddenData (tc, k) tvs p = HidingDataDecl p tc k tvs
  hiddenClass (_, _, cx, (qcls, k), tv) ids p = HidingClassDecl p cx qcls k tv ids

-- |Parser for an interface data declaration
iDataDecl :: Parser a Token IDecl
iDataDecl = iTypeDeclLhs IDataDecl KW_data <*> constrs <*> iHiddenPragma
  where constrs = equals <-*> constrDecl `sepBy1` bar `opt` []

-- |Parser for an interface newtype declaration
iNewtypeDecl :: Parser a Token IDecl
iNewtypeDecl = iTypeDeclLhs INewtypeDecl KW_newtype
               <*-> equals <*> newConstrDecl <*> iHiddenPragma

-- |Parser for an interface type synonym declaration
iTypeDecl :: Parser a Token IDecl
iTypeDecl = iTypeDeclLhs ITypeDecl KW_type
            <*-> equals <*> type0

-- |Parser for an interface hiding pragma
iHiddenPragma :: Parser a Token [Ident]
iHiddenPragma = token PragmaHiding
                <-*> (con `sepBy` comma)
                <*-> token PragmaEnd
                `opt` []

-- |Parser for an interface function declaration
iFunctionDecl :: Parser a Token IDecl
iFunctionDecl = IFunctionDecl <$> position <*> qfun <*> option iMethodPragma
                <*> arity <*-> token DoubleColon <*> qualType
                          <*-> token ColonQ <*> detExpr

-- |Parser for an interface method pragma
iMethodPragma :: Parser a Token Ident
iMethodPragma = token PragmaMethod <-*> clsvar <*-> token PragmaEnd

-- |Parser for function's arity
arity :: Parser a Token Int
arity = int `opt` 0

iTypeDeclLhs :: (Position -> QualIdent -> Maybe KindExpr -> [Ident] -> a)
             -> Category -> Parser b Token a
iTypeDeclLhs f kw = f' <$> tokenPos kw <*> withKind qtycon <*> many tyvar
  where f' p (tc, k) = f p tc k

-- |Parser for an interface class declaration
iClassDecl :: Parser a Token IDecl
iClassDecl = (\(sp, _, cx, (qcls, k), tv) ->
               IClassDecl (span2Pos sp) cx qcls k tv)
        <$> classInstHead KW_class (withKind qtycls) clsvar
        <*> braces (iMethod `sepBy` semicolon)
        <*> iClassHidden

-- |Parser for an interface method declaration
iMethod :: Parser a Token IMethodDecl
iMethod = IMethodDecl <$> position
                      <*> fun <*> option int <*-> token DoubleColon <*> qualType
                                             <*-> token ColonQ <*> detExpr
                                             <*> option iDefaultMethodDetType

  where iDefaultMethodDetType = token ColonQ <-*> detExpr

-- |Parser for an interface hiding pragma
iClassHidden :: Parser a Token [Ident]
iClassHidden = token PragmaHiding
          <-*> (fun `sepBy` comma)
          <*-> token PragmaEnd
          `opt` []

-- |Parser for an interface instance declaration
iInstanceDecl :: Parser a Token IDecl
iInstanceDecl = (\(sp, _, cx, qcls, inst) ->
                   IInstanceDecl (span2Pos sp) cx qcls inst)
           <$> classInstHead KW_instance qtycls type2
           <*> braces (iImpl `sepBy` semicolon)
           <*> option iModulePragma

-- |Parser for an interface method implementation
iImpl :: Parser a Token IMethodImpl
iImpl = mkIImpl <$> fun <*> ((impl <$> arity <*-> token ColonQ <*> detExpr)
                        <|> (notImpl <$> (token Underscore <-*> token ColonQ <-*> detExpr)))
  where
    mkIImpl i f = f i
    impl  a d i = (i, Just a , d)
    notImpl d i = (i, Nothing, d)

iModulePragma :: Parser a Token ModuleIdent
iModulePragma = token PragmaModule <-*> modIdent <*-> token PragmaEnd

-- ---------------------------------------------------------------------------
-- Top-Level Declarations
-- ---------------------------------------------------------------------------

topDecls :: Parser a Token ([Decl ()], [Span])
topDecls = topDecl `sepBySp` semicolon

topDecl :: Parser a Token (Decl ())
topDecl = choice [ dataDecl, externalDataDecl, newtypeDecl, typeDecl
                 , classDecl, instanceDecl, defaultDecl
                 , infixDecl, functionDecl ]

dataDecl :: Parser a Token (Decl ())
dataDecl = combineWithSpans
             <$> typeDeclLhs dataDecl' KW_data
             <*> ((addSpan <$> tokenSpan Equals <*> constrs) `opt` ([],[]))
             <*> deriv
  where constrs = constrDecl `sepBy1Sp` bar
        dataDecl' sp = DataDecl (spanInfo sp [sp])

externalDataDecl :: Parser a Token (Decl ())
externalDataDecl = decl <$> tokenSpan KW_external <*> typeDeclLhs (,,) KW_data
  where decl sp1 (sp2, tc, tvs) = updateEndPos $
          ExternalDataDecl (spanInfo sp1 [sp1, sp2]) tc tvs

newtypeDecl :: Parser a Token (Decl ())
newtypeDecl = combineWithSpans
             <$> typeDeclLhs newtypeDecl' KW_newtype
             <*> ((\sp c -> (c, [sp]))  <$> tokenSpan Equals <*> newConstrDecl)
             <*> deriv
  where newtypeDecl' sp = NewtypeDecl (spanInfo sp [sp])

combineWithSpans :: HasSpanInfo a =>
                    (t1 -> t2 -> a) -> (t1, [Span]) -> (t2, [Span]) -> a
combineWithSpans df (cs, sps1) (cls, sps2)
  = updateEndPos $ setSrcInfoPoints (getSrcInfoPoints res ++ sps1 ++ sps2) res
  where res = df cs cls

typeDecl :: Parser a Token (Decl ())
typeDecl = typeDeclLhs typeDecl' KW_type <*> tokenSpan Equals <*> type0
  where typeDecl' sp1 tyc tyv sp2 txp = updateEndPos $
          TypeDecl (spanInfo sp1 [sp1, sp2]) tyc tyv txp

typeDeclLhs :: (Span -> Ident -> [Ident] -> a) -> Category
            -> Parser b Token a
typeDeclLhs f kw = f <$> tokenSpan kw <*> tycon <*> many anonOrTyvar

constrDecl :: Parser a Token ConstrDecl
constrDecl = spanPosition <**> constr
  where
  constr =  conId     <**> identDecl
        <|> tokenSpan LeftParen <**> parenDecl
        <|> type1 <\> conId <\> leftParen <**> opDecl
  identDecl =  many type2 <**> (conType <$> opDecl `opt` conDecl)
           <|> recDecl <$> recFields
  parenDecl =  conOpDeclPrefix
           <$> conSym    <*>   tokenSpan RightParen <*> type2 <*> type2
           <|> tupleType <**> (tokenSpan RightParen <**> opDeclParen)
  opDecl = conOpDecl <$> conop <*> type1
  opDeclParen = conOpDeclParen <$> conop <*> type1
  recFields = layoutOff <-*> bracesSp (fieldDecl `sepBySp` comma)
  conType f tys c = f $ foldl mkApply (mkConstructorType $ qualify c) tys
  mkApply t1 t2 = updateEndPos $ ApplyType (fromSrcSpan (getSrcSpan t1)) t1 t2
  mkConstructorType qid = ConstructorType (fromSrcSpan (getSrcSpan qid)) qid
  conDecl tys c sp = updateEndPos $
    ConstrDecl (SpanInfo sp []) c tys
  conOpDecl op ty2 ty1 sp = updateEndPos $
    ConOpDecl (SpanInfo sp []) ty1 op ty2
  conOpDeclParen op ty2 sp1 ty1 sp2 sp5 = updateEndPos $
    ConOpDecl (SpanInfo sp5 [sp2, sp1]) ty1 op ty2
  conOpDeclPrefix op sp1 ty1 ty2 sp2 sp3 = updateEndPos $
    ConOpDecl (SpanInfo sp3 [sp2, sp1]) ty1 op ty2
  recDecl ((fs, ss), sp1, sp2) c sp3 = updateEndPos $
    RecordDecl (SpanInfo sp3 (sp1 : ss ++ [sp2])) c fs

fieldDecl :: Parser a Token FieldDecl
fieldDecl = mkFieldDecl <$> spanPosition <*> labels
                        <*> tokenSpan DoubleColon <*> type0
  where labels = fun `sepBy1Sp` comma
        mkFieldDecl sp1 (idt,ss) sp2 ty = updateEndPos $
          FieldDecl (spanInfo sp1 (ss ++ [sp2])) idt ty

newConstrDecl :: Parser a Token NewConstrDecl
newConstrDecl = spanPosition <**> (con <**> newConstr)
  where newConstr =  newConDecl <$> type2
                 <|> newRecDecl <$> newFieldDecl
        newConDecl ty  c sp = updateEndPos $ NewConstrDecl (spanInfo sp []) c ty
        newRecDecl ((idt, sp2, ty), sp3, sp4) c sp1 = updateEndPos $
          NewRecordDecl (spanInfo sp1 [sp3,sp2,sp4]) c (idt, ty)

newFieldDecl :: Parser a Token ((Ident, Span, TypeExpr), Span, Span)
newFieldDecl = layoutOff <-*> bracesSp labelDecl
  where labelDecl = (,,) <$> fun <*> tokenSpan DoubleColon <*> type0

deriv :: Parser a Token ([QualIdent], [Span])
deriv = (addSpan <$> tokenSpan KW_deriving <*> classes) `opt` ([], [])
  where classes = ((\q -> ([q], [])) <$> qtycls)
               <|> ((\sp1 (qs, ss) sp2 -> (qs, sp1 : (ss ++ [sp2])))
                      <$> tokenSpan LeftParen
                      <*> (qtycls `sepBySp` comma)
                      <*> tokenSpan RightParen)

functionDecl :: Parser a Token (Decl ())
functionDecl = spanPosition <**> decl
  where decl = fun `sepBy1Sp` comma <**> funListDecl <|?> funRule

funRule :: Parser a Token (Span -> Decl ())
funRule = mkFunDecl <$> lhs <*> declRhs
  where lhs = (\f ->
                 (f, updateEndPos $ FunLhs (fromSrcSpan (getSrcSpan f)) f []))
                 <$> fun <|?> funLhs

funListDecl :: Parser a Token (([Ident],[Span]) -> Span -> Decl ())
funListDecl = typeSig <|> detSig <|> mkExtFun <$> tokenSpan KW_external
  where mkExtFun sp1 (vs,ss) sp2 = updateEndPos $
          ExternalDecl (spanInfo sp2 (ss++[sp1])) (map (Var ()) vs)

detSig :: Parser a Token (([Ident],[Span]) -> Span -> Decl ())
detSig = sig <$> tokenSpan ColonQ <*> detExpr
  where
    sig :: Span -> DetExpr -> ([Ident], [Span]) -> Span -> Decl ()
    sig colons dty (vs, commas) sp = updateEndPos $
      DetSig (spanInfo sp (sp : commas ++ [colons])) vs dty

-- detExpr ::= detExpr -> ...
detExpr :: Parser a Token DetExpr
detExpr = detExpr0 `chainr1` arrowDetExpr

-- arrowDetExpr ::= ->
arrowDetExpr :: Parser a Token (DetExpr -> DetExpr -> DetExpr)
arrowDetExpr = mkArrow <$> tokenSpan RightArrow
  where mkArrow sp1 d1 d2 = updateEndPos $
          ArrowDetExpr (spanInfo sp1 [sp1]) d1 d2

-- detExpr0 ::= (detExpr) | D | ND | tyvar
-- note that we actually parse D and ND as tyvars
-- and then convert them later.
detExpr0 :: Parser a Token DetExpr
detExpr0 =  (pExpr <$> spanPosition <*> parensSp detExpr)
        <|> (vExpr <$> spanPosition <*> tyvar)
  where
    pExpr sp1 (dty, sp2, sp3) = updateEndPos $
      ParenDetExpr (spanInfo sp1 [sp2, sp3]) dty
    dExpr sp = DetDetExpr (spanInfo sp [sp])
    ndExpr sp = AnyDetExpr (spanInfo sp [sp])
    vExpr sp tv = case idName tv of
      "Det" -> dExpr sp
      "Any" -> ndExpr sp
      _     -> updateEndPos $ VarDetExpr (spanInfo sp []) tv

typeSig :: Parser a Token (([Ident],[Span]) -> Span -> Decl ())
typeSig = sig <$> tokenSpan DoubleColon <*> qualType
  where sig sp1 qty (vs,ss) sp2 = updateEndPos $
          TypeSig (spanInfo sp2 (ss++[sp1])) vs qty

mkFunDecl :: (Ident, Lhs ()) -> Rhs () -> Span -> Decl ()
mkFunDecl (f, lhs) rhs' p = updateEndPos $
    FunctionDecl (spanInfo p []) () f [updateEndPos $
                                         Equation (spanInfo p []) lhs rhs']

funLhs :: Parser a Token (Ident, Lhs ())
funLhs = mkFunLhs    <$> fun      <*> many1 pattern2
    <|?> flip ($ updateEndPos) <$> pattern1 <*> opLhs
    <|?> curriedLhs
  where
  opLhs  =                opLHS funSym (gConSym <\> funSym)
       <|> tokenSpan Backquote <**>
             opLHSSp ((,) <$> funId            <*>  spanPosition
                                               <*-> expectBackquote)
                     ((,) <$> qConId <\> funId <*>  spanPosition
                                               <*-> expectBackquote)
  opLHS funP consP   = mkOpLhs       <$> funP  <*> pattern0
                    <|> mkInfixPat   <$> consP <*> pattern1 <*> opLhs
  opLHSSp funP consP = mkOpLhsSp     <$> funP  <*> pattern0
                    <|> mkInfixPatSp <$> consP <*> pattern1 <*> opLhs
  mkFunLhs f ts = (f , updateEndPos $ FunLhs (fromSrcSpan (getSrcSpan f)) f ts)
  mkOpLhs op t2 f t1      =
    let t1' = f t1
    in (op, updateEndPos $ OpLhs (fromSrcSpan (getSrcSpan t1')) t1' op t2)
  mkInfixPat op t2 f g t1 =
    f (g . InfixPattern (fromSrcSpan (getSrcSpan t1)) () t1 op) t2
  mkOpLhsSp (op, sp1)    t2   sp2 f t1 =
    let t1' = f t1
    in (op, updateEndPos $
              OpLhs (spanInfo (getSrcSpan t1') [sp2, sp1]) t1' op t2)

  mkInfixPatSp (op, sp1) t2 g sp2 f t1 =
    g (f . InfixPattern (spanInfo (getSrcSpan t1) [sp2, sp1]) () t1 op) t2


curriedLhs :: Parser a Token (Ident, Lhs ())
curriedLhs = apLhs <$> parensSp funLhs <*> many1 pattern2
  where apLhs ((f, lhs), sp1, sp2) ts =
          let spi = fromSrcSpan sp1
          in (f, updateEndPos $ setSrcInfoPoints [sp1, sp2] $ ApLhs spi lhs ts)

declRhs :: Parser a Token (Rhs ())
declRhs = rhs equals

rhs :: Parser a Token b -> Parser a Token (Rhs ())
rhs eq = rhsExpr <*> localDecls
  where rhsExpr =  mkSimpleRhs  <$> spanPosition <*-> eq <*> expr
               <|> mkGuardedRhs <$> spanPosition <*>  many1 (condExpr eq)
        mkSimpleRhs  sp1 e  (Just sp2, ds, li) = updateEndPos $
          SimpleRhs  (SpanInfo sp1 [sp1, sp2]) li e ds
        mkSimpleRhs  sp1 e  (Nothing, ds, li) = updateEndPos $
          SimpleRhs  (SpanInfo sp1 [sp1]) li e ds
        mkGuardedRhs sp1 ce (Just sp2, ds, li) = updateEndPos $
          GuardedRhs (SpanInfo sp1 [sp1, sp2]) li ce ds
        mkGuardedRhs sp1 ce (Nothing, ds, li) = updateEndPos $
          GuardedRhs (SpanInfo sp1 [sp1]) li ce ds

whereClause :: Parser a Token b -> Parser a Token (Maybe Span, [b], LayoutInfo)
whereClause decl = (\sp (ds, li) -> (Just sp, ds, li))
  <$> tokenSpan KW_where
  <*> layoutWhere decl `opt` (Nothing, [], WhitespaceLayout)

localDecls :: Parser a Token (Maybe Span, [Decl ()], LayoutInfo)
localDecls = whereClause valueOrInfixDecl

valueDecls :: Parser a Token ([Decl ()], [Span])
valueDecls = valueOrInfixDecl `sepBySp` semicolon

valueOrInfixDecl :: Parser a Token (Decl ())
valueOrInfixDecl = choice [infixDecl, valueDecl]

infixDecl :: Parser a Token (Decl ())
infixDecl = infixDeclLhs infixDecl'
              <*> option ((,) <$> spanPosition <*> integer)
              <*> funop `sepBy1Sp` comma
  where infixDecl' sp1 inf (Just (sp2, pr)) (ids, ss) =
          updateEndPos $ InfixDecl (spanInfo sp1 (sp1:sp2:ss)) inf (Just pr) ids
        infixDecl' sp1 inf Nothing          (ids, ss) =
          updateEndPos $ InfixDecl (spanInfo sp1 (sp1    :ss)) inf Nothing   ids

infixDeclLhs :: (Span -> Infix -> a) -> Parser b Token a
infixDeclLhs f = f <$> spanPosition <*> tokenOps infixKW
  where infixKW = [(KW_infix, Infix), (KW_infixl, InfixL), (KW_infixr, InfixR)]

valueDecl :: Parser a Token (Decl ())
valueDecl = spanPosition <**> decl
  where
  decl =   var `sepBy1Sp` comma       <**> valListDecl
      <|?> patOrFunDecl <$> pattern0   <*> declRhs
      <|?> mkFunDecl    <$> curriedLhs <*> declRhs

  valListDecl =  funListDecl
             <|> mkFree <$> tokenSpan KW_free
    where mkFree sp1 (vs, ss) sp2 = updateEndPos $
            FreeDecl (spanInfo sp2 (ss ++ [sp1])) (map (Var ()) vs)

  patOrFunDecl (ConstructorPattern spi _ c ts)
    | not (isConstrId c) = mkFunDecl (f, FunLhs spi f ts)
    where f = unqualify c
  patOrFunDecl t = patOrOpDecl updateEndPos t

  patOrOpDecl f (InfixPattern spi a t1 op t2)
    | isConstrId op = patOrOpDecl (f . InfixPattern spi a t1 op) t2
    | otherwise     = mkFunDecl (op', updateEndPos $ OpLhs spi (f t1) op' t2)
    where op' = unqualify op
  patOrOpDecl f t = mkPatDecl (f t)

  mkPatDecl t rhs' sp = updateEndPos $ PatternDecl (fromSrcSpan sp) t rhs'

  isConstrId c = c == qConsId || isQualified c || isQTupleId c

defaultDecl :: Parser a Token (Decl ())
defaultDecl = mkDefaultDecl <$> tokenSpan KW_default
                            <*> parensSp (type0 `sepBySp` comma)
  where mkDefaultDecl sp1 ((ty, ss), sp2, sp3) = updateEndPos $
          DefaultDecl (spanInfo sp1 (sp1 : sp2 : (ss ++ [sp3]))) ty

classInstHead :: Category -> Parser a Token b -> Parser a Token c
              -> Parser a Token (Span, [Span], Context, b, c)
classInstHead kw cls ty = f <$> tokenSpan kw
                            <*> optContext (,,) ((,) <$> cls <*> ty)
  where f sp (cx, ss, (cls', ty')) = (sp, ss, cx, cls', ty')

classDecl :: Parser a Token (Decl ())
classDecl = mkClass
        <$> classInstHead KW_class tycls clsvar
        <*> whereClause innerDecl
  where
    --TODO: Support infixDecl
    innerDecl = foldr1 (<|?>)
      [ spanPosition <**> (fun `sepBy1Sp` comma <**> (typeSig <|> detSig))
      , spanPosition <**> funRule
      {-, infixDecl-} ]
    mkClass (sp1, ss, cx, cls, tv) (Just sp2, ds, li) = updateEndPos $
      ClassDecl (SpanInfo sp1 (sp1 : (ss ++ [sp2]))) li cx cls tv ds
    mkClass (sp1, ss, cx, cls, tv) (Nothing, ds, li) = updateEndPos $
      ClassDecl (SpanInfo sp1 (sp1 : ss)) li cx cls tv ds

instanceDecl :: Parser a Token (Decl ())
instanceDecl = mkInstance
           <$> classInstHead KW_instance qtycls type2
           <*> whereClause innerDecl
  where
    innerDecl = spanPosition <**> funRule
    mkInstance (sp1, ss, cx, qcls, inst) (Just sp2, ds, li) = updateEndPos $
      InstanceDecl (SpanInfo sp1 (sp1 : (ss ++ [sp2]))) li cx qcls inst ds
    mkInstance (sp1, ss, cx, qcls, inst) (Nothing, ds, li) = updateEndPos $
      InstanceDecl (SpanInfo sp1 (sp1 : ss)) li cx qcls inst ds
-- ---------------------------------------------------------------------------
-- Type classes
-- ---------------------------------------------------------------------------

optContext :: (Context -> [Span] -> a -> b)
           -> Parser c Token a
           -> Parser c Token b
optContext f p = combine <$> context <*> tokenSpan DoubleArrow <*> p
            <|?> f [] [] <$> p
  where combine (ctx, ss) sp = f ctx (ss ++ [sp])

context :: Parser a Token (Context, [Span])
context = (\c -> ([c], [])) <$> constraint
      <|> combine <$> parensSp (constraint `sepBySp` comma)
  where combine ((ctx, ss), sp1, sp2) = (ctx, sp1 : (ss ++ [sp2]))

constraint :: Parser a Token Constraint
constraint = mkConstraint <$> spanPosition <*> qtycls <*> conType
  where varType = mkVariableType <$> spanPosition <*> clsvar
        conType = fmap ((,) []) varType
               <|> mk <$> parensSp
                            (foldl mkApplyType <$> varType <*> many1 type2)
        mkConstraint sp qtc (ss, ty) = updateEndPos $
          Constraint (spanInfo sp ss) qtc ty
        mkVariableType sp = VariableType (fromSrcSpan sp)
        mkApplyType t1 t2 =
          ApplyType (fromSrcSpan (combineSpans (getSrcSpan t1)
                                               (getSrcSpan t2)))
                    t1 t2
        mk (a, sp1, sp2) = ([sp1, sp2], a)

-- ---------------------------------------------------------------------------
-- Kinds
-- ---------------------------------------------------------------------------

withKind :: Parser a Token b -> Parser a Token (b, Maybe KindExpr)
withKind p = implicitKind <$> p
        <|?> parens (explicitKind <$> p <*-> token DoubleColon <*> kind0)
  where implicitKind x   = (x, Nothing)
        explicitKind x k = (x, Just k)

-- kind0 ::= kind1 ['->' kind0]
kind0 :: Parser a Token KindExpr
kind0 = kind1 `chainr1` (ArrowKind <$-> token RightArrow)

-- kind1 ::= * | '(' kind0 ')'
kind1 :: Parser a Token KindExpr
kind1 = Star <$-> token SymStar
    <|> parens kind0

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- qualType ::= [context '=>']  type0
qualType :: Parser a Token QualTypeExpr
qualType = mkQualTypeExpr <$> spanPosition <*> optContext (,,) type0
  where mkQualTypeExpr sp (cx, ss, ty) = updateEndPos $
          QualTypeExpr (spanInfo sp ss) cx ty

-- type0 ::= type1 ['->' type0]
type0 :: Parser a Token TypeExpr
type0 = type1 `chainr1` (mkArrowType <$> tokenSpan RightArrow)
  where mkArrowType sp ty1 ty2 = updateEndPos $
          ArrowType (spanInfo (getSrcSpan ty1) [sp]) ty1 ty2

-- type1 ::= [type1] type2
type1 :: Parser a Token TypeExpr
type1 = foldl1 mkApplyType <$> many1 type2
  where mkApplyType ty1 ty2 = updateEndPos $
          ApplyType (fromSrcSpan (getSrcSpan ty1)) ty1 ty2

-- type2 ::= anonType | identType | parenType | bracketType
type2 :: Parser a Token TypeExpr
type2 = anonType <|> identType <|> parenType <|> bracketType

-- anonType ::= '_'
anonType :: Parser a Token TypeExpr
anonType = mkVariableType <$> spanPosition <*> anonIdent
  where mkVariableType sp = VariableType (fromSrcSpan sp)

-- identType ::= <identifier>
identType :: Parser a Token TypeExpr
identType =  mkVariableType    <$> spanPosition <*> tyvar
         <|> mkConstructorType <$> spanPosition <*> qtycon <\> tyvar
  where mkVariableType    sp = VariableType    (fromSrcSpan sp)
        mkConstructorType sp = ConstructorType (fromSrcSpan sp)

-- parenType ::= '(' tupleType ')'
parenType :: Parser a Token TypeExpr
parenType = fmap updateSpanWithBrackets (parensSp tupleType)

-- tupleType ::= type0                         (parenthesized type)
--            |  type0 ',' type0 { ',' type0 } (tuple type)
--            |  '->'                          (function type constructor)
--            |  ',' { ',' }                   (tuple type constructor)
--            |                                (unit type)
tupleType :: Parser a Token TypeExpr
tupleType = type0 <**> (mkTuple <$> many1 ((,) <$> tokenSpan Comma <*> type0)
                          `opt` ParenType NoSpanInfo)
        <|> tokenSpan RightArrow <**> succeed (mkConstructorType qArrowId)
        <|> mkConstructorTupleType <$> many1 (tokenSpan Comma)
        <|> succeed (ConstructorType NoSpanInfo qUnitId)
  where mkTuple stys ty = let (ss, tys) = unzip stys
                          in TupleType (fromSrcInfoPoints ss) (ty : tys)
        mkConstructorType qid sp = ConstructorType (fromSrcInfoPoints [sp]) qid
        mkConstructorTupleType ss = ConstructorType (fromSrcInfoPoints ss)
                                                    (qTupleId (length ss + 1))

-- bracketType ::= '[' listType ']'
bracketType :: Parser a Token TypeExpr
bracketType = fmap updateSpanWithBrackets (bracketsSp listType)

-- listType ::= type0 (list type)
--           |        (list type constructor)
listType :: Parser a Token TypeExpr
listType = ListType NoSpanInfo <$> type0
             `opt` ConstructorType NoSpanInfo qListId

-- ---------------------------------------------------------------------------
-- Literals
-- ---------------------------------------------------------------------------

-- literal ::= '\'' <escaped character> '\''
--          |  <integer>
--          |  <float>
--          |  '"' <escaped string> '"'
literal :: Parser a Token Literal
literal = Char   <$> char
      <|> Int    <$> integer
      <|> Float  <$> float
      <|> String <$> string

-- ---------------------------------------------------------------------------
-- Patterns
-- ---------------------------------------------------------------------------

-- pattern0 ::= pattern1 [ gconop pattern0 ]
pattern0 :: Parser a Token (Pattern ())
pattern0 = pattern1 `chainr1` (mkInfixPattern <$> gconop)
  where mkInfixPattern qid p1 p2 =
          InfixPattern (fromSrcSpan (combineSpans (getSrcSpan p1)
                                                  (getSrcSpan p2)))
            () p1 qid p2

-- pattern1 ::= varId
--           |  QConId { pattern2 }
--           |  '-'  Integer
--           |  '(' parenPattern'
--           | pattern2
pattern1 :: Parser a Token (Pattern ())
pattern1 = varId <**> identPattern'            -- unqualified
        <|> qConId <\> varId <**> constrPattern -- qualified
        <|> mkNegNum <$> minus <*> negNum
        <|> tokenSpan LeftParen <**> parenPattern'
        <|> pattern2  <\> qConId <\> leftParen
  where
  identPattern' =  optAsRecPattern
               <|> mkConsPattern qualify <$> many1 pattern2

  constrPattern =  mkConsPattern id <$> many1 pattern2
               <|> optRecPattern


  parenPattern' =  minus <**> minusPattern
      <|> mkGconPattern <$> gconId <*> tokenSpan RightParen <*> many pattern2
      <|> mkFunIdentP <$> funSym <\> minus <*> tokenSpan RightParen
                                           <*> identPattern'
      <|> mkParenTuple <$> parenTuplePattern <\> minus <*> tokenSpan RightParen
  minusPattern = flip mkParenMinus <$> tokenSpan RightParen <*> identPattern'
         <|> mkParenMinus <$> parenMinusPattern <*> tokenSpan RightParen

  mkNegNum idt = setEndPosition (end (getSrcSpan idt))
  mkParenTuple p sp1 sp2 =
    setSpanInfo (spanInfo (combineSpans sp2 sp1) [sp2, sp1]) p
  mkFunIdentP idt sp1 f sp2 = setSrcSpan (combineSpans sp2 sp1) (f idt)
  mkParenMinus f sp1 idt sp2 = setSrcSpan (combineSpans sp2 sp1) (f idt)
  mkConsPattern f ts c = updateEndPos $
    ConstructorPattern (fromSrcSpan (getSrcSpan (f c))) () (f c) ts
  mkGconPattern qid sp1 ps sp2 = updateEndPos $
    ConstructorPattern (spanInfo (getSrcSpan qid) [sp2,sp1]) () qid ps

pattern2 :: Parser a Token (Pattern ())
pattern2 =  literalPattern <|> anonPattern <|> identPattern
        <|> parenPattern   <|> listPattern <|> lazyPattern

-- literalPattern ::= <integer> | <char> | <float> | <string>
literalPattern :: Parser a Token (Pattern ())
literalPattern = flip LiteralPattern () <$> fmap fromSrcSpan spanPosition
                                        <*> literal

-- anonPattern ::= '_'
anonPattern :: Parser a Token (Pattern ())
anonPattern = flip VariablePattern () <$> fmap fromSrcSpan spanPosition
                                      <*> anonIdent

-- identPattern ::= Variable [ '@' pattern2 | '{' fields '}'
--               |  qConId   [ '{' fields '}' ]
identPattern :: Parser a Token (Pattern ())
identPattern =  varId <**> optAsRecPattern -- unqualified
            <|> qConId <\> varId <**> optRecPattern               -- qualified

-- parenPattern ::= '(' '-' minusPattern              -- e.g. (-5), (-4 + x), etc...
--               |  "TupleConstructor"                -- in prefix notation, e.g. (,,,)
--               |  '(' funSymbol ')' optAsRecPattern -- e.g. (<<>)@p
--               |  '(' parenTuplePattern ')'         -- e.g. (x,y,z), (p)
--
-- minusPattern ::= ')' optAsRecPattern               -- if you want to shadow "-" locally
--               |  parenMinusPattern ')'             -- e.g. -x), -x + y), etc...
parenPattern :: Parser a Token (Pattern ())
parenPattern = tokenSpan LeftParen <**> parenPattern'
  where
  parenPattern' = minus <**> minusPattern
      <|> mkConstructorPattern <$> gconId <*> tokenSpan RightParen
      <|> mkFunAsRec <$> funSym <\> minus <*> tokenSpan RightParen
                     <*> optAsRecPattern
      <|> mkParenTuple <$> parenTuplePattern <\> minus <*> tokenSpan RightParen
  minusPattern = mkOptAsRec <$> tokenSpan RightParen <*> optAsRecPattern
      <|> mkParen <$> parenMinusPattern <*> tokenSpan RightParen

  mkConstructorPattern qid sp1 sp2 =
    ConstructorPattern (fromSrcSpan (combineSpans sp2 sp1)) () qid []
  mkFunAsRec = flip (flip . mkOptAsRec)
  mkParenTuple p sp1 sp2 =
    let ss  = getSrcInfoPoints p
        spi = spanInfo (combineSpans sp2 sp1) (sp2 : (ss ++ [sp1]))
    in setSpanInfo spi p
  mkOptAsRec sp1 f idt sp2 =
    let p   = f idt
        ss  = getSrcInfoPoints p
        spi = spanInfo (combineSpans sp2 sp1) ([sp2, sp1] ++ ss)
    in setSpanInfo spi p
  mkParen f sp1 idt sp2 =
    let p   = f idt
        ss  = getSrcInfoPoints p
        spi = spanInfo (combineSpans sp2 sp1) (sp2 : (ss ++ [sp1]))
    in setSpanInfo spi p

-- listPattern ::= '[' pattern0s ']'
-- pattern0s   ::= {- empty -}
--              |  pattern0 ',' pattern0s
listPattern :: Parser a Token (Pattern ())
listPattern = mkListPattern <$> bracketsSp (pattern0 `sepBySp` comma)
  where mkListPattern ((ps, ss), sp1, sp2) = updateEndPos $
          ListPattern (spanInfo sp1 (sp1 : (ss ++ [sp2]))) () ps

-- lazyPattern ::= '~' pattern2
lazyPattern :: Parser a Token (Pattern ())
lazyPattern = mkLazyPattern <$> tokenSpan Tilde <*> pattern2
  where mkLazyPattern sp p = updateEndPos $ LazyPattern (spanInfo sp [sp]) p

-- optRecPattern ::= [ '{' fields '}' ]
optRecPattern :: Parser a Token (QualIdent -> Pattern ())
optRecPattern = mkRecordPattern <$> fieldsSp pattern0 `opt` mkConPattern
  where
  mkRecordPattern ((fs, ss), sp1, sp2) c = updateEndPos $
    RecordPattern (spanInfo (getSrcSpan c) (sp1 : (ss ++ [sp2]))) () c fs
  mkConPattern c = ConstructorPattern (fromSrcSpan (getSrcSpan c)) () c []

-- ---------------------------------------------------------------------------
-- Partial patterns used in the combinators above, but also for parsing
-- the left-hand side of a declaration.
-- ---------------------------------------------------------------------------

gconId :: Parser a Token QualIdent
gconId = colon <|> tupleCommas

negNum :: Parser a Token (Pattern ())
negNum = mkNegativePattern <$> spanPosition <*>
                             (Int <$> integer <|> Float <$> float)
  where mkNegativePattern sp = NegativePattern (fromSrcSpan sp) ()

optAsRecPattern :: Parser a Token (Ident -> Pattern ())
optAsRecPattern =  mkAsPattern     <$> tokenSpan At <*> pattern2
               <|> mkRecordPattern <$> fieldsSp pattern0
               `opt` mkVariablePattern
  where mkRecordPattern ((fs,ss),sp1,sp2) v =
          let s = getPosition v
              e = end sp2
              f = file s
              spi = spanInfo (Span f s e) (sp1 : (ss ++ [sp2]))
          in updateEndPos $ RecordPattern spi () (qualify v) fs
        mkAsPattern sp p idt =
          AsPattern (spanInfo (getSrcSpan idt) [sp]) idt p
        mkVariablePattern idt =
          VariablePattern (fromSrcSpan (getSrcSpan idt)) () idt

optInfixPattern :: Parser a Token (Pattern () -> Pattern ())
optInfixPattern = mkInfixPat <$> gconop <*> pattern0
            `opt` id
  where mkInfixPat op t2 t1 =
          let s = getPosition t1
              e = getSrcSpanEnd t2
              f = file s
          in InfixPattern (fromSrcSpan (Span f s e)) () t1 op t2

optTuplePattern :: Parser a Token (Pattern () -> Pattern ())
optTuplePattern = mkTuple <$> many1 ((,) <$> tokenSpan Comma <*> pattern0)
            `opt` ParenPattern NoSpanInfo
  where mkTuple ts t = let (ss, ps) = unzip ts
                       in TuplePattern (fromSrcInfoPoints ss) (t:ps)

parenMinusPattern :: Parser a Token (Ident -> Pattern ())
parenMinusPattern = mkNeg <$> negNum <.> optInfixPattern <.> optTuplePattern
  where mkNeg neg idt = setEndPosition (end (getSrcSpan idt)) neg

parenTuplePattern :: Parser a Token (Pattern ())
parenTuplePattern = pattern0 <**> optTuplePattern
              `opt` ConstructorPattern NoSpanInfo () qUnitId []

-- ---------------------------------------------------------------------------
-- Expressions
-- ---------------------------------------------------------------------------

-- condExpr ::= '|' expr0 eq expr
--
-- Note: The guard is an `expr0` instead of `expr` since conditional expressions
-- may also occur in case expressions, and an expression like
-- @
-- case a of { _ -> True :: Bool -> a }
-- @
-- can not be parsed with a limited parser lookahead.
condExpr :: Parser a Token b -> Parser a Token (CondExpr ())
condExpr eq = mkCondExpr <$> spanPosition <*-> bar <*> expr0
                         <*> spanPosition <*-> eq  <*> expr
  where mkCondExpr sp1 e1 sp2 e2 = updateEndPos $
          CondExpr (spanInfo sp1 [sp1, sp2]) e1 e2

-- expr ::= expr0 [ '::' type0 ]
expr :: Parser a Token (Expression ())
expr = expr0 <??> (mkTyped <$> tokenSpan DoubleColon <*> qualType)
  where mkTyped sp qty e = updateEndPos $ setSrcSpan (getSrcSpan e) $
          Typed (fromSrcInfoPoints [sp]) e qty

-- expr0 ::= expr1 { infixOp expr1 }
expr0 :: Parser a Token (Expression ())
expr0 = expr1 `chainr1` (mkInfixApply <$> infixOp)
  where mkInfixApply op e1 e2 = InfixApply
          (fromSrcSpan (combineSpans (getSrcSpan e1) (getSrcSpan e2))) e1 op e2

-- expr1 ::= - expr2 | expr2
expr1 :: Parser a Token (Expression ())
expr1 =  mkUnaryMinus <$> minus <*> expr2
     <|> expr2
  where mkUnaryMinus idt ex =
          let p = getPosition idt
              e = getSrcSpanEnd ex
              f = file p
          in UnaryMinus (spanInfo (Span f p e) [Span f p (incr p 1)]) ex

-- expr2 ::= lambdaExpr | letExpr | doExpr | ifExpr | caseExpr | expr3
expr2 :: Parser a Token (Expression ())
expr2 = choice [ lambdaExpr, letExpr, doExpr, ifExpr, caseExpr
               , foldl1 mkApply <$> many1 expr3
               ]
  where mkApply e1 e2 = updateEndPos $ Apply (fromSrcSpan (getSrcSpan e1)) e1 e2

expr3 :: Parser a Token (Expression ())
expr3 = foldl mkRecordUpdate <$> expr4 <*> many recUpdate
  where recUpdate = layoutOff <-*> bracesSp (field expr0 `sepBy1Sp` comma)
        mkRecordUpdate e ((fs,ss), sp1, sp2) = updateEndPos $
          setSrcInfoPoints (sp1 : (ss ++ [sp2])) $
          RecordUpdate (fromSrcSpan (getSrcSpan e)) e fs

expr4 :: Parser a Token (Expression ())
expr4 = choice
  [constant, anonFreeVariable, variable, parenExpr, listExpr]

constant :: Parser a Token (Expression ())
constant = mkLiteral <$> spanPosition <*> literal
  where mkLiteral sp = Literal (fromSrcSpan sp) ()

anonFreeVariable :: Parser a Token (Expression ())
anonFreeVariable =  (\ p v -> mkVariable $ qualify $ addPositionIdent p v)
                <$> position <*> anonIdent
  where mkVariable qid = Variable (fromSrcSpan (getSrcSpan qid)) () qid

variable :: Parser a Token (Expression ())
variable = qFunId <**> optRecord
  where optRecord = mkRecord <$> fieldsSp expr0 `opt` mkVariable
        mkRecord ((fs,ss), sp1, sp2) qid =
          let spi = spanInfo (getSrcSpan qid) (sp1 : (ss ++ [sp2]))
          in updateEndPos $ Record spi () qid fs
        mkVariable qid = Variable (fromSrcSpan (getSrcSpan qid)) () qid

parenExpr :: Parser a Token (Expression ())
parenExpr = fmap updateSpanWithBrackets (parensSp pExpr)
  where
  pExpr = minus <**> minusOrTuple
      <|> mkConstructor () <$> tupleCommas
      <|> leftSectionOrTuple <\> minus
      <|> opOrRightSection <\> minus
      `opt` Constructor (fromSrcInfoPoints []) () qUnitId
  minusOrTuple = mkUnaryMinus <$> expr1 <.> infixOrTuple
            `opt` mkVariable . qualify
  leftSectionOrTuple = expr1 <**> infixOrTuple
  infixOrTuple = ($ updateEndPos) <$> infixOrTuple'
  infixOrTuple' = infixOp <**> leftSectionOrExp
              <|> (.) <$> (optType <.> tupleExpr)
  leftSectionOrExp = expr1 <**> (infixApp <$> infixOrTuple')
                `opt` leftSection
  optType   = mkTyped <$> tokenSpan DoubleColon <*> qualType `opt` id
  tupleExpr = mkTuple <$> many1 ((,) <$> tokenSpan Comma <*> expr)
               `opt` Paren NoSpanInfo
  opOrRightSection =  qFunSym <**> optRightSection
                  <|> colon   <**> optCRightSection
                  <|> infixOp <\> colon <\> qFunSym <**> rightSection
  optRightSection  = (. InfixOp ()    ) <$> rightSection
                       `opt` Variable NoSpanInfo ()
  optCRightSection = (. InfixConstr ()) <$> rightSection
                       `opt` Constructor NoSpanInfo ()
  rightSection     = mkRightSection <$> expr0
  infixApp f e2 op g e1 = f (g . mkInfixApply e1 op) e2
  leftSection op f e = mkLeftSection (f e) op
  mkTuple ses e = let (ss,es) = unzip ses
                  in Tuple (fromSrcInfoPoints ss) (e:es)
  mkConstructor = Constructor NoSpanInfo
  mkTyped sp ty e = Typed (fromSrcInfoPoints [sp]) e ty
  mkRightSection = flip (RightSection NoSpanInfo)
  mkLeftSection  = LeftSection  NoSpanInfo
  mkInfixApply e1 op e2 = InfixApply (fromSrcSpan
    (combineSpans (getSrcSpan e1) (getSrcSpan e2))) e1 op e2
  mkVariable = Variable NoSpanInfo ()
  mkUnaryMinus ex idt =
    let p = getPosition idt
        e = getSrcSpanEnd ex
        f = file p
    in UnaryMinus (spanInfo (Span f p e) [Span f p (incr p 1)]) ex

infixOp :: Parser a Token (InfixOp ())
infixOp = InfixOp () <$> qfunop <|> InfixConstr () <$> colon

listExpr :: Parser a Token (Expression ())
listExpr = updateSpanWithBrackets <$>
             bracketsSp (elements `opt` List (fromSrcInfoPoints []) () [])
  where
  elements = expr <**> rest
  rest = comprehension
      <|> enumeration mkEnumFromTo mkEnumFrom
      <|> (tokenSpan Comma <**> (expr <**>(
           enumeration mkEnumFromThenTo mkEnumFromThen
          <|> list <$> many ((,) <$> tokenSpan Comma <*> expr)))
    `opt` (\ e -> List (fromSrcInfoPoints []) () [e]))
  comprehension = mkListCompr <$> tokenSpan Bar <*> quals
  enumeration enumTo enum =
    tokenSpan DotDot <**> (enumTo <$> expr `opt` enum)

  mkEnumFrom                 sp     =
    EnumFrom (fromSrcInfoPoints [sp])
  mkEnumFromTo            e1 sp  e2 =
    EnumFromTo (fromSrcInfoPoints [sp]) e2 e1
  mkEnumFromThen      sp1 e1 sp2 e2 =
    EnumFromThen (fromSrcInfoPoints [sp2,sp1]) e2 e1
  mkEnumFromThenTo e1 sp1 e2 sp2 e3 =
    EnumFromThenTo (fromSrcInfoPoints [sp2,sp1]) e3 e2 e1
  mkListCompr sp qu e = ListCompr (fromSrcInfoPoints [sp]) e qu

  list xs e2 sp e1 = let (ss, es) = unzip xs
                     in List (fromSrcInfoPoints (sp:ss)) () (e1:e2:es)

updateSpanWithBrackets :: HasSpanInfo a => (a, Span, Span) -> a
updateSpanWithBrackets (ex, sp1, sp2) =
  let ss = getSrcInfoPoints ex
      s  = getPosition sp1
      e  = end sp2
      f  = file s
      spi = spanInfo (Span f s e) (sp1 : (ss ++ [sp2]))
  in setSpanInfo spi ex

lambdaExpr :: Parser a Token (Expression ())
lambdaExpr = mkLambda <$> tokenSpan Backslash <*> many1 pattern2
                      <*> spanPosition <*-> expectRightArrow
                      <*> expr
  where mkLambda sp1 ps sp2 e = updateEndPos $ Lambda (spanInfo sp1 [sp1, sp2]) ps e

letExpr :: Parser a Token (Expression ())
letExpr = mkLet <$>  tokenSpan KW_let <*> layout valueDecls
                <*> (tokenSpan KW_in <?> "in expected") <*> expr
  where
    mkLet sp1 (ds, lay) sp2 e = updateEndPos $
      Let (spanInfo sp1 [sp1, sp2])lay ds e

doExpr :: Parser a Token (Expression ())
doExpr = mkDo <$> tokenSpan KW_do <*> layout stmts
  where
    mkDo sp ((stms, ex), lay) = updateEndPos $
      Do (spanInfo sp [sp]) lay stms ex

ifExpr :: Parser a Token (Expression ())
ifExpr = mkIfThenElse
    <$>  tokenSpan KW_if                        <*> expr
    <*> (tokenSpan KW_then <?> "then expected") <*> expr
    <*> (tokenSpan KW_else <?> "else expected") <*> expr
  where mkIfThenElse sp1 e1 sp2 e2 sp3 e3 = updateEndPos $
          IfThenElse (spanInfo sp1 [sp1, sp2, sp3]) e1 e2 e3

caseExpr :: Parser a Token (Expression ())
caseExpr = (mkCase Flex  <$> tokenSpan KW_fcase
        <|> mkCase Rigid <$> tokenSpan KW_case)
          <*> expr
          <*> (tokenSpan KW_of <?> "of expected")
          <*> layout (alt `sepBy1Sp` semicolon)
  where
    mkCase ct sp1 e sp2 (alts, lay) = updateEndPos $
      Case (spanInfo sp1 [sp1, sp2]) lay ct e alts

alt :: Parser a Token (Alt ())
alt = mkAlt <$> spanPosition <*> pattern0
            <*> spanPosition <*> rhs expectRightArrow
  where mkAlt sp1 p sp2 = updateEndPos . Alt (spanInfo sp1 [sp2]) p

fieldsSp :: Parser a Token b -> Parser a Token (([Field b], [Span]), Span, Span)
fieldsSp p = layoutOff <-*> bracesSp (field p `sepBySp` comma)

field :: Parser a Token b -> Parser a Token (Field b)
field p = mkField <$> spanPosition <*> qfun
                  <*> spanPosition <*-> expectEquals
                  <*> p
  where mkField sp1 q sp2 = updateEndPos . Field (spanInfo sp1 [sp2]) q

-- ---------------------------------------------------------------------------
-- \paragraph{Statements in list comprehensions and \texttt{do} expressions}
-- Parsing statements is a bit difficult because the syntax of patterns
-- and expressions largely overlaps. The parser will first try to
-- recognize the prefix \emph{Pattern}~\texttt{<-} of a binding statement
-- and if this fails fall back into parsing an expression statement. In
-- addition, we have to be prepared that the sequence
-- \texttt{let}~\emph{LocalDefs} can be either a let-statement or the
-- prefix of a let expression.
-- ---------------------------------------------------------------------------

stmts :: Parser a Token (([Statement ()], Expression ()), [Span])
stmts = stmt reqStmts optStmts

reqStmts :: Parser a Token (Statement ()
                        -> (([Statement ()], Expression ()), [Span]))
reqStmts = mkStmts <$> spanPosition <*-> semicolon <*> stmts
  where mkStmts sp ((sts, e), sps) st = ((st : sts, e), sp:sps)

optStmts :: Parser a Token (Expression ()
                        -> (([Statement ()], Expression ()), [Span]))
optStmts = succeed mkStmtExpr <.> reqStmts `opt` (\e -> (([], e), []))
  where mkStmtExpr e = StmtExpr (fromSrcSpan (getSrcSpan e)) e

quals :: Parser a Token [Statement ()]
quals = stmt (succeed id) (succeed mkStmtExpr) `sepBy1` comma
  where mkStmtExpr e = StmtExpr (fromSrcSpan (getSrcSpan e)) e

stmt :: Parser a Token (Statement () -> b)
     -> Parser a Token (Expression () -> b) -> Parser a Token b
stmt stmtCont exprCont =  letStmt stmtCont exprCont
                      <|> exprOrBindStmt stmtCont exprCont

letStmt :: Parser a Token (Statement () -> b)
        -> Parser a Token (Expression () -> b) -> Parser a Token b
letStmt stmtCont exprCont = ((,) <$> tokenSpan KW_let <*> layout valueDecls)
                              <**> optExpr
  where optExpr =  let' <$> tokenSpan KW_in <*> expr <.> exprCont
               <|> succeed stmtDecl' <.> stmtCont
          where
            let' sp1 e (sp2, (ds, lay)) = updateEndPos $
              Let (spanInfo sp2 [sp2, sp1]) lay ds e
            stmtDecl'  (sp2, (ds, lay)) = updateEndPos $
              StmtDecl (spanInfo sp2 [sp2]) lay ds

exprOrBindStmt :: Parser a Token (Statement () -> b)
               -> Parser a Token (Expression () -> b)
               -> Parser a Token b
exprOrBindStmt stmtCont exprCont =
       stmtBind' <$> spanPosition <*> pattern0 <*> tokenSpan LeftArrow <*> expr
         <**> stmtCont
  <|?> expr <\> token KW_let <**> exprCont
  where
    stmtBind' sp1 p sp2 e = updateEndPos $
      StmtBind (spanInfo sp1 [sp2]) p e

-- ---------------------------------------------------------------------------
-- Goals
-- ---------------------------------------------------------------------------

goal :: Parser a Token (Goal ())
goal = mkGoal <$> spanPosition <*> expr <*> localDecls
  where
    mkGoal sp1 ex (Just sp2, ds, li) = updateEndPos $
      Goal (SpanInfo sp1 [sp2]) li ex ds
    mkGoal sp1 ex (Nothing, ds, li) = updateEndPos $
            Goal (SpanInfo sp1 []) li ex ds

-- ---------------------------------------------------------------------------
-- Literals, identifiers, and (infix) operators
-- ---------------------------------------------------------------------------

char :: Parser a Token Char
char = cval <$> token CharTok

float :: Parser a Token Double
float = fval <$> token FloatTok

int :: Parser a Token Int
int = fromInteger <$> integer

integer :: Parser a Token Integer
integer = ival <$> token IntTok

string :: Parser a Token String
string = sval <$> token StringTok

tycon :: Parser a Token Ident
tycon = conId

anonOrTyvar :: Parser a Token Ident
anonOrTyvar = anonIdent <|> tyvar

tyvar :: Parser a Token Ident
tyvar = varId

clsvar :: Parser a Token Ident
clsvar = tyvar

tycls :: Parser a Token Ident
tycls = conId

qtycls :: Parser a Token QualIdent
qtycls = qConId

qtycon :: Parser a Token QualIdent
qtycon = qConId

varId :: Parser a Token Ident
varId = ident

funId :: Parser a Token Ident
funId = ident

conId :: Parser a Token Ident
conId = ident

funSym :: Parser a Token Ident
funSym = sym

conSym :: Parser a Token Ident
conSym = sym

modIdent :: Parser a Token ModuleIdent
modIdent = mIdent <?> "module name expected"

var :: Parser a Token Ident
var = varId <|> updateSpanWithBrackets
                     <$> parensSp (funSym <?> "operator symbol expected")

fun :: Parser a Token Ident
fun = funId <|> updateSpanWithBrackets
                     <$> parensSp (funSym <?> "operator symbol expected")

con :: Parser a Token Ident
con = conId <|> updateSpanWithBrackets
                     <$> parensSp (conSym <?> "operator symbol expected")

funop :: Parser a Token Ident
funop = funSym <|> updateSpanWithBrackets
                     <$> backquotesSp (funId <?> "operator name expected")

conop :: Parser a Token Ident
conop = conSym <|> updateSpanWithBrackets
                     <$> backquotesSp (conId <?> "operator name expected")

qFunId :: Parser a Token QualIdent
qFunId = qIdent

qConId :: Parser a Token QualIdent
qConId = qIdent

qFunSym :: Parser a Token QualIdent
qFunSym = qSym

qConSym :: Parser a Token QualIdent
qConSym = qSym

gConSym :: Parser a Token QualIdent
gConSym = qConSym <|> colon

qfun :: Parser a Token QualIdent
qfun = qFunId <|> updateSpanWithBrackets
                     <$> parensSp (qFunSym <?> "operator symbol expected")

qfunop :: Parser a Token QualIdent
qfunop = qFunSym <|> updateSpanWithBrackets
                     <$> backquotesSp (qFunId <?> "operator name expected")

gconop :: Parser a Token QualIdent
gconop = gConSym <|> updateSpanWithBrackets
                     <$> backquotesSp (qConId <?> "operator name expected")

anonIdent :: Parser a Token Ident
anonIdent = (`setSpanInfo` anonId) . fromSrcSpanBoth <$> tokenSpan Underscore

mIdent :: Parser a Token ModuleIdent
mIdent = mIdent' <$> spanPosition <*>
     tokens [Id,QId,Id_as,Id_ccall,Id_forall,Id_hiding,
             Id_interface,Id_primitive,Id_qualified]
  where mIdent' sp a = ModuleIdent (fromSrcSpanBoth sp) (modulVal a ++ [sval a])

ident :: Parser a Token Ident
ident = (\ sp t -> setSpanInfo (fromSrcSpanBoth sp) (mkIdent (sval t)))
          <$> spanPosition <*> tokens [Id,Id_as,Id_ccall,Id_forall,Id_hiding,
                                       Id_interface,Id_primitive,Id_qualified]

qIdent :: Parser a Token QualIdent
qIdent = qualify <$> ident <|> qIdentWith QId

sym :: Parser a Token Ident
sym = (\ sp t -> setSpanInfo (fromSrcSpanBoth sp) (mkIdent (sval t)))
        <$> spanPosition <*> tokens [Sym, SymDot, SymMinus, SymStar]

qSym :: Parser a Token QualIdent
qSym = qualify <$> sym <|> qIdentWith QSym

qIdentWith :: Category -> Parser a Token QualIdent
qIdentWith c = mkQIdent <$> spanPosition <*> token c
  where mkQIdent :: Span -> Attributes -> QualIdent
        mkQIdent sp a =
          let mid  = ModuleIdent (fromSrcSpan sp) (modulVal a)
              p    = incr (getPosition sp) (mIdentLength mid - 1)
              mid' = setEndPosition p mid
              idt  = setSrcSpan sp $ mkIdent (sval a)
              idt' = setPosition (incr p 1) idt
          in QualIdent (fromSrcSpanBoth sp) (Just mid') idt'

colon :: Parser a Token QualIdent
colon = qualify . (`setSpanInfo` consId) . fromSrcSpanBoth <$> tokenSpan Colon

minus :: Parser a Token Ident
minus = (`setSpanInfo` minusId) . fromSrcSpanBoth <$> tokenSpan SymMinus

tupleCommas :: Parser a Token QualIdent
tupleCommas = (\ sp ss -> qualify $ updateEndPos $ setSpanInfo (spanInfo sp ss)
                                  $ tupleId      $ succ $ length  ss)
              <$> spanPosition <*> many1 (tokenSpan Comma)

-- ---------------------------------------------------------------------------
-- Layout
-- ---------------------------------------------------------------------------

-- |This function starts a new layout block but does not wait for its end.
-- This is only used for parsing the module header.
startLayout :: Parser a Token (b, [Span]) -> Parser a Token (b, LayoutInfo)
startLayout p =  layoutOff <-*>
                   (createExpli1Layout <$> tokenSpan LeftBrace <*> p)
             <|> layoutOn  <-*>
                   (createWhiteLayout  <$> p)

layout :: Parser a Token (b, [Span]) -> Parser a Token (b, LayoutInfo)
layout p =  (createExpliLayout
              <$> (layoutOff <-*> bracesSp p))
        <|> (createWhiteLayout
              <$> (layoutOn  <-*> p <*-> (token VRightBrace <|> layoutEnd)))

createExpli1Layout :: Span -> (b, [Span]) -> (b, LayoutInfo)
createExpli1Layout sp1 (b, ss) = (b, ExplicitLayout (sp1:ss))

createExpliLayout :: ((b, [Span]), Span, Span) -> (b, LayoutInfo)
createExpliLayout ((b, ss), sp1, spe) = (b, ExplicitLayout (sp1:ss ++ [spe]))

createWhiteLayout :: (b, [Span]) -> (b, LayoutInfo)
createWhiteLayout (b, _) = (b, WhitespaceLayout)

-- We have to remove an additional context on an empty where-clause
layoutWhere :: Parser a Token b -> Parser a Token ([b], LayoutInfo)
layoutWhere p =  (createExpliLayout
                    <$> (layoutOff <-*> bracesSp (p `sepBySp` semicolon)))
             <|> (createWhiteLayout
                    <$> (layoutOn  <-*> (p `sepBy1Sp` semicolon)
                                   <*-> (token VRightBrace <|> layoutEnd)))
             <|> succeed ([], WhitespaceLayout)

-- ---------------------------------------------------------------------------
-- Bracket combinators
-- ---------------------------------------------------------------------------

braces :: Parser a Token b -> Parser a Token b
braces p = between leftBrace p rightBrace

bracesSp :: Parser a Token b -> Parser a Token (b, Span, Span)
bracesSp p = (\sp1 b sp2 -> (b, sp1, sp2))
               <$> tokenSpan LeftBrace
               <*> p
               <*> tokenSpan RightBrace

bracketsSp :: Parser a Token b -> Parser a Token (b, Span, Span)
bracketsSp p = (\sp1 b sp2 -> (b, sp1, sp2))
                 <$> tokenSpan LeftBracket
                 <*> p
                 <*> tokenSpan RightBracket

parens :: Parser a Token b -> Parser a Token b
parens p = between leftParen p rightParen

parensSp :: Parser a Token b -> Parser a Token (b, Span, Span)
parensSp p = (\sp1 b sp2 -> (b, sp1, sp2))
               <$> tokenSpan LeftParen
               <*> p
               <*> tokenSpan RightParen

backquotesSp :: Parser a Token b -> Parser a Token (b, Span, Span)
backquotesSp p = (\sp1 b sp2 -> (b, sp1, sp2))
                   <$> tokenSpan Backquote
                   <*> p
                   <*> spanPosition <*-> expectBackquote

-- ---------------------------------------------------------------------------
-- Simple token parsers
-- ---------------------------------------------------------------------------

token :: Category -> Parser a Token Attributes
token c = attr <$> symbol (Token c NoAttributes)
  where attr (Token _ a) = a

tokens :: [Category] -> Parser a Token Attributes
tokens = foldr1 (<|>) . map token

tokenPos :: Category -> Parser a Token Position
tokenPos c = position <*-> token c

tokenSpan :: Category -> Parser a Token Span
tokenSpan c = spanPosition <*-> token c

tokenOps :: [(Category, b)] -> Parser a Token b
tokenOps cs = ops [(Token c NoAttributes, x) | (c, x) <- cs]

comma :: Parser a Token Attributes
comma = token Comma

semicolon :: Parser a Token Attributes
semicolon = token Semicolon <|> token VSemicolon

bar :: Parser a Token Attributes
bar = token Bar

equals :: Parser a Token Attributes
equals = token Equals

expectEquals :: Parser a Token Attributes
expectEquals = equals <?> "= expected"

expectWhere :: Parser a Token Attributes
expectWhere = token KW_where <?> "where expected"

expectRightArrow :: Parser a Token Attributes
expectRightArrow  = token RightArrow <?> "-> expected"

backquote :: Parser a Token Attributes
backquote = token Backquote

expectBackquote :: Parser a Token Attributes
expectBackquote = backquote <?> "backquote (`) expected"

leftParen :: Parser a Token Attributes
leftParen = token LeftParen

rightParen :: Parser a Token Attributes
rightParen = token RightParen

leftBrace :: Parser a Token Attributes
leftBrace = token LeftBrace

rightBrace :: Parser a Token Attributes
rightBrace = token RightBrace
