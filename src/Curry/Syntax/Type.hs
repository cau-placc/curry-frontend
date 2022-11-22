{- |
    Module      :  $Header$
    Description :  Abstract syntax for Curry
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2014        Jan Rasmus Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the necessary data structures to maintain the
    parsed representation of a Curry program.
-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
module Curry.Syntax.Type
  ( -- * Module header
    Module (..)
    -- ** Module pragmas
  , ModulePragma (..), Extension (..), KnownExtension (..), Tool (..), KnownTool (..)
    -- ** Export specification
  , ExportSpec (..), Export (..)
    -- ** Import declarations
  , ImportDecl (..), ImportSpec (..), Import (..), Qualified
    -- * Interface
  , Interface (..), IImportDecl (..), Arity, IDecl (..), KindExpr (..)
  , IMethodDecl (..), IMethodImpl
    -- * Declarations
  , Decl (..), Precedence, Infix (..), ConstrDecl (..), NewConstrDecl (..)
  , FieldDecl (..)
  , TypeExpr (..), QualTypeExpr (..)
  , Equation (..), Lhs (..), Rhs (..), CondExpr (..)
  , Literal (..), Pattern (..), Expression (..), InfixOp (..)
  , Statement (..), CaseType (..), Alt (..), Field (..), Var (..)
    -- * Type classes
  , Context, Constraint (..), InstanceType
    -- * Goals
  , Goal (..)
  ) where

import Data.Binary            (Binary)
import GHC.Generics           (Generic)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Span
import Curry.Base.Pretty      (Pretty(..))

import Curry.Syntax.Extension

import Text.PrettyPrint

-- ---------------------------------------------------------------------------
-- Modules
-- ---------------------------------------------------------------------------

-- |Curry module
data Module a = Module SpanInfo LayoutInfo [ModulePragma] ModuleIdent
                       (Maybe ExportSpec) [ImportDecl] [Decl a]
    deriving (Eq, Read, Show, Generic, Binary)

-- |Module pragma
data ModulePragma
  = LanguagePragma SpanInfo [Extension]         -- ^ language pragma
  | OptionsPragma  SpanInfo (Maybe Tool) String -- ^ options pragma
    deriving (Eq, Read, Show, Generic, Binary)

-- |Export specification
data ExportSpec = Exporting SpanInfo [Export]
    deriving (Eq, Read, Show, Generic, Binary)

-- |Single exported entity
data Export
  = Export         SpanInfo QualIdent         -- f/T
  | ExportTypeWith SpanInfo QualIdent [Ident] -- T (C1,...,Cn)
  | ExportTypeAll  SpanInfo QualIdent         -- T (..)
  | ExportModule   SpanInfo ModuleIdent       -- module M
    deriving (Eq, Read, Show, Generic, Binary)

-- |Import declaration
data ImportDecl = ImportDecl SpanInfo ModuleIdent Qualified
                             (Maybe ModuleIdent) (Maybe ImportSpec)
    deriving (Eq, Read, Show, Generic, Binary)

-- |Flag to signal qualified import
type Qualified = Bool

-- |Import specification
data ImportSpec
  = Importing SpanInfo [Import]
  | Hiding    SpanInfo [Import]
    deriving (Eq, Read, Show, Generic, Binary)

-- |Single imported entity
data Import
  = Import         SpanInfo Ident            -- f/T
  | ImportTypeWith SpanInfo Ident [Ident]    -- T (C1,...,Cn)
  | ImportTypeAll  SpanInfo Ident            -- T (..)
    deriving (Eq, Read, Show, Generic, Binary)

-- ---------------------------------------------------------------------------
-- Module interfaces
-- ---------------------------------------------------------------------------

-- | Module interface
--
-- Interface declarations are restricted to type declarations and signatures.
-- Note that an interface function declaration additionaly contains the
-- function arity (= number of parameters) in order to generate
-- correct FlatCurry function applications.
data Interface = Interface ModuleIdent [IImportDecl] [IDecl]
    deriving (Eq, Read, Show, Generic, Binary)

-- |Interface import declaration
data IImportDecl = IImportDecl Position ModuleIdent
    deriving (Eq, Read, Show, Generic, Binary)

-- |Arity of a function
type Arity = Int

-- |Interface declaration
data IDecl
  = IInfixDecl      Position Infix Precedence QualIdent
  | HidingDataDecl  Position QualIdent (Maybe KindExpr) [Ident]
  | IDataDecl       Position QualIdent (Maybe KindExpr) [Ident] [ConstrDecl]  [Ident]
  | INewtypeDecl    Position QualIdent (Maybe KindExpr) [Ident] NewConstrDecl [Ident]
  | ITypeDecl       Position QualIdent (Maybe KindExpr) [Ident] TypeExpr
  | IFunctionDecl   Position QualIdent (Maybe Ident) Arity QualTypeExpr
  | HidingClassDecl Position Context QualIdent (Maybe KindExpr) Ident
  | IClassDecl      Position Context QualIdent (Maybe KindExpr) Ident [IMethodDecl] [Ident]
  | IInstanceDecl   Position Context QualIdent InstanceType [IMethodImpl] (Maybe ModuleIdent)
    deriving (Eq, Read, Show, Generic, Binary)

-- |Class methods
data IMethodDecl = IMethodDecl Position Ident (Maybe Arity) QualTypeExpr
  deriving (Eq, Read, Show, Generic, Binary)

-- |Class method implementations
type IMethodImpl = (Ident, Arity)

-- |Kind expressions
data KindExpr
  = Star
  | ArrowKind KindExpr KindExpr
    deriving (Eq, Read, Show, Generic, Binary)

-- ---------------------------------------------------------------------------
-- Declarations (local or top-level)
-- ---------------------------------------------------------------------------

-- |Declaration in a module
data Decl a
  = InfixDecl        SpanInfo Infix (Maybe Precedence) [Ident]                   -- infixl 5 (op), `fun`
  | DataDecl         SpanInfo Ident [Ident] [ConstrDecl] [QualIdent]             -- data C a b = C1 a | C2 b deriving (D, ...)
  | ExternalDataDecl SpanInfo Ident [Ident]                                      -- external data C a b
  | NewtypeDecl      SpanInfo Ident [Ident] NewConstrDecl [QualIdent]            -- newtype C a b = C a b deriving (D, ...)
  | TypeDecl         SpanInfo Ident [Ident] TypeExpr                             -- type C a b = D a b
  | TypeSig          SpanInfo [Ident] QualTypeExpr                               -- f, g :: Bool
  | FunctionDecl     SpanInfo a Ident [Equation a]                               -- f True = 1 ; f False = 0
  | ExternalDecl     SpanInfo [Var a]                                            -- f, g external
  | PatternDecl      SpanInfo (Pattern a) (Rhs a)                                -- Just x = ...
  | FreeDecl         SpanInfo [Var a]                                            -- x, y free
  | DefaultDecl      SpanInfo [TypeExpr]                                         -- default (Int, Float)
  | ClassDecl        SpanInfo LayoutInfo Context Ident Ident [Decl a]            -- class C a => D a where {TypeSig|InfixDecl|FunctionDecl}
  | InstanceDecl     SpanInfo LayoutInfo Context QualIdent InstanceType [Decl a] -- instance C a => M.D (N.T a b c) where {FunctionDecl}
    deriving (Eq, Read, Show, Generic, Binary)

-- ---------------------------------------------------------------------------
-- Infix declaration
-- ---------------------------------------------------------------------------

-- |Operator precedence
type Precedence = Integer

-- |Fixity of operators
data Infix
  = InfixL -- ^ left-associative
  | InfixR -- ^ right-associative
  | Infix  -- ^ no associativity
    deriving (Eq, Read, Show, Generic, Binary)

-- |Constructor declaration for algebraic data types
data ConstrDecl
  = ConstrDecl SpanInfo Ident [TypeExpr]
  | ConOpDecl  SpanInfo TypeExpr Ident TypeExpr
  | RecordDecl SpanInfo Ident [FieldDecl]
    deriving (Eq, Read, Show, Generic, Binary)

-- |Constructor declaration for renaming types (newtypes)
data NewConstrDecl
  = NewConstrDecl SpanInfo Ident TypeExpr
  | NewRecordDecl SpanInfo Ident (Ident, TypeExpr)
   deriving (Eq, Read, Show, Generic, Binary)

-- |Declaration for labelled fields
data FieldDecl = FieldDecl SpanInfo [Ident] TypeExpr
  deriving (Eq, Read, Show, Generic, Binary)

-- |Type expressions
data TypeExpr
  = ConstructorType SpanInfo QualIdent
  | ApplyType       SpanInfo TypeExpr TypeExpr
  | VariableType    SpanInfo Ident
  | TupleType       SpanInfo [TypeExpr]
  | ListType        SpanInfo TypeExpr
  | ArrowType       SpanInfo TypeExpr TypeExpr
  | ParenType       SpanInfo TypeExpr
  | ForallType      SpanInfo [Ident] TypeExpr
    deriving (Eq, Read, Show, Generic, Binary)

-- |Qualified type expressions
data QualTypeExpr = QualTypeExpr SpanInfo Context TypeExpr
    deriving (Eq, Read, Show, Generic, Binary)

-- ---------------------------------------------------------------------------
-- Type classes
-- ---------------------------------------------------------------------------

type Context = [Constraint]

data Constraint = Constraint SpanInfo QualIdent TypeExpr
    deriving (Eq, Read, Show, Generic, Binary)

type InstanceType = TypeExpr

-- ---------------------------------------------------------------------------
-- Functions
-- ---------------------------------------------------------------------------

-- |Function defining equation
data Equation a = Equation SpanInfo (Lhs a) (Rhs a)
    deriving (Eq, Read, Show, Generic, Binary)

-- |Left-hand-side of an 'Equation' (function identifier and patterns)
data Lhs a
  = FunLhs SpanInfo Ident [Pattern a]             -- f x y
  | OpLhs  SpanInfo (Pattern a) Ident (Pattern a) -- x $ y
  | ApLhs  SpanInfo (Lhs a) [Pattern a]           -- ($) x y
    deriving (Eq, Read, Show, Generic, Binary)

-- |Right-hand-side of an 'Equation'
data Rhs a
  = SimpleRhs  SpanInfo LayoutInfo (Expression a) [Decl a] -- @expr where decls@
  | GuardedRhs SpanInfo LayoutInfo [CondExpr a]   [Decl a] -- @| cond = expr where decls@
    deriving (Eq, Read, Show, Generic, Binary)

-- |Conditional expression (expression conditioned by a guard)
data CondExpr a = CondExpr SpanInfo (Expression a) (Expression a)
    deriving (Eq, Read, Show, Generic, Binary)

-- |Literal
data Literal
  = Char   Char
  | Int    Integer
  | Float  Double
  | String String
    deriving (Eq, Read, Show, Generic, Binary)

-- |Constructor term (used for patterns)
data Pattern a
  = LiteralPattern     SpanInfo a Literal
  | NegativePattern    SpanInfo a Literal
  | VariablePattern    SpanInfo a Ident
  | ConstructorPattern SpanInfo a QualIdent [Pattern a]
  | InfixPattern       SpanInfo a (Pattern a) QualIdent (Pattern a)
  | ParenPattern       SpanInfo (Pattern a)
  | RecordPattern      SpanInfo a QualIdent [Field (Pattern a)] -- C { l1 = p1, ..., ln = pn }
  | TuplePattern       SpanInfo [Pattern a]
  | ListPattern        SpanInfo a [Pattern a]
  | AsPattern          SpanInfo Ident (Pattern a)
  | LazyPattern        SpanInfo (Pattern a)
  | FunctionPattern    SpanInfo a QualIdent [Pattern a]
  | InfixFuncPattern   SpanInfo a (Pattern a) QualIdent (Pattern a)
    deriving (Eq, Read, Show, Generic, Binary)

-- |Expression
data Expression a
  = Literal           SpanInfo a Literal
  | Variable          SpanInfo a QualIdent
  | Constructor       SpanInfo a QualIdent
  | Paren             SpanInfo (Expression a)
  | Typed             SpanInfo (Expression a) QualTypeExpr
  | Record            SpanInfo a QualIdent [Field (Expression a)]    -- C {l1 = e1,..., ln = en}
  | RecordUpdate      SpanInfo (Expression a) [Field (Expression a)] -- e {l1 = e1,..., ln = en}
  | Tuple             SpanInfo [Expression a]
  | List              SpanInfo a [Expression a]
  | ListCompr         SpanInfo (Expression a) [Statement a]   -- the ref corresponds to the main list
  | EnumFrom          SpanInfo (Expression a)
  | EnumFromThen      SpanInfo (Expression a) (Expression a)
  | EnumFromTo        SpanInfo (Expression a) (Expression a)
  | EnumFromThenTo    SpanInfo (Expression a) (Expression a) (Expression a)
  | UnaryMinus        SpanInfo (Expression a)
  | Apply             SpanInfo (Expression a) (Expression a)
  | InfixApply        SpanInfo (Expression a) (InfixOp a) (Expression a)
  | LeftSection       SpanInfo (Expression a) (InfixOp a)
  | RightSection      SpanInfo (InfixOp a) (Expression a)
  | Lambda            SpanInfo [Pattern a] (Expression a)
  | Let               SpanInfo LayoutInfo [Decl a] (Expression a)
  | Do                SpanInfo LayoutInfo [Statement a] (Expression a)
  | IfThenElse        SpanInfo (Expression a) (Expression a) (Expression a)
  | Case              SpanInfo LayoutInfo CaseType (Expression a) [Alt a]
    deriving (Eq, Read, Show, Generic, Binary)

-- |Infix operation
data InfixOp a
  = InfixOp     a QualIdent
  | InfixConstr a QualIdent
    deriving (Eq, Read, Show, Generic, Binary)

-- |Statement (used for do-sequence and list comprehensions)
data Statement a
  = StmtExpr SpanInfo (Expression a)
  | StmtDecl SpanInfo LayoutInfo [Decl a]
  | StmtBind SpanInfo (Pattern a) (Expression a)
    deriving (Eq, Read, Show, Generic, Binary)

-- |Type of case expressions
data CaseType
  = Rigid
  | Flex
    deriving (Eq, Read, Show, Generic, Binary)

-- |Single case alternative
data Alt a = Alt SpanInfo (Pattern a) (Rhs a)
    deriving (Eq, Read, Show, Generic, Binary)

-- |Record field
data Field a = Field SpanInfo QualIdent a
    deriving (Eq, Read, Show, Generic, Binary)

-- |Annotated identifier
data Var a = Var a Ident
    deriving (Eq, Read, Show, Generic, Binary)

-- ---------------------------------------------------------------------------
-- Goals
-- ---------------------------------------------------------------------------

-- |Goal in REPL (expression to evaluate)
data Goal a = Goal SpanInfo LayoutInfo (Expression a) [Decl a]
    deriving (Eq, Read, Show, Generic, Binary)

-- ---------------------------------------------------------------------------
-- instances
-- ---------------------------------------------------------------------------

instance Functor Module where
  fmap f (Module sp li ps m es is ds) = Module sp li ps m es is (map (fmap f) ds)

instance Functor Decl where
  fmap _ (InfixDecl sp fix prec ops) = InfixDecl sp fix prec ops
  fmap _ (DataDecl sp tc tvs cs clss) = DataDecl sp tc tvs cs clss
  fmap _ (ExternalDataDecl sp tc tvs) = ExternalDataDecl sp tc tvs
  fmap _ (NewtypeDecl sp tc tvs nc clss) = NewtypeDecl sp tc tvs nc clss
  fmap _ (TypeDecl sp tc tvs ty) = TypeDecl sp tc tvs ty
  fmap _ (TypeSig sp fs qty) = TypeSig sp fs qty
  fmap f (FunctionDecl sp a f' eqs) = FunctionDecl sp (f a) f' (map (fmap f) eqs)
  fmap f (ExternalDecl sp vs) = ExternalDecl sp (map (fmap f) vs)
  fmap f (PatternDecl sp t rhs) = PatternDecl sp (fmap f t) (fmap f rhs)
  fmap f (FreeDecl sp vs) = FreeDecl sp (map (fmap f) vs)
  fmap _ (DefaultDecl sp tys) = DefaultDecl sp tys
  fmap f (ClassDecl sp li cx cls clsvar ds) =
    ClassDecl sp li cx cls clsvar (map (fmap f) ds)
  fmap f (InstanceDecl sp li cx qcls inst ds) =
    InstanceDecl sp li cx qcls inst (map (fmap f) ds)

instance Functor Equation where
  fmap f (Equation p lhs rhs) = Equation p (fmap f lhs) (fmap f rhs)

instance Functor Lhs where
  fmap f (FunLhs p f' ts) = FunLhs p f' (map (fmap f) ts)
  fmap f (OpLhs p t1 op t2) = OpLhs p (fmap f t1) op (fmap f t2)
  fmap f (ApLhs p lhs ts) = ApLhs p (fmap f lhs) (map (fmap f) ts)

instance Functor Rhs where
  fmap f (SimpleRhs p li e ds) = SimpleRhs p li (fmap f e) (map (fmap f) ds)
  fmap f (GuardedRhs p li cs ds) = GuardedRhs p li (map (fmap f) cs) (map (fmap f) ds)

instance Functor CondExpr where
  fmap f (CondExpr p g e) = CondExpr p (fmap f g) (fmap f e)

instance Functor Pattern where
  fmap f (LiteralPattern p a l) = LiteralPattern p (f a) l
  fmap f (NegativePattern p a l) = NegativePattern p (f a) l
  fmap f (VariablePattern p a v) = VariablePattern p (f a) v
  fmap f (ConstructorPattern p a c ts) =
    ConstructorPattern p (f a) c (map (fmap f) ts)
  fmap f (InfixPattern p a t1 op t2) =
    InfixPattern p (f a) (fmap f t1) op (fmap f t2)
  fmap f (ParenPattern p t) = ParenPattern p (fmap f t)
  fmap f (RecordPattern p a c fs) =
    RecordPattern p (f a) c (map (fmap (fmap f)) fs)
  fmap f (TuplePattern p ts) = TuplePattern p (map (fmap f) ts)
  fmap f (ListPattern p a ts) = ListPattern p (f a) (map (fmap f) ts)
  fmap f (AsPattern p v t) = AsPattern p v (fmap f t)
  fmap f (LazyPattern p t) = LazyPattern p (fmap f t)
  fmap f (FunctionPattern p a f' ts) =
    FunctionPattern p (f a) f' (map (fmap f) ts)
  fmap f (InfixFuncPattern p a t1 op t2) =
    InfixFuncPattern p (f a) (fmap f t1) op (fmap f t2)

instance Functor Expression where
  fmap f (Literal p a l) = Literal p (f a) l
  fmap f (Variable p a v) = Variable p (f a) v
  fmap f (Constructor p a c) = Constructor p (f a) c
  fmap f (Paren p e) = Paren p (fmap f e)
  fmap f (Typed p e qty) = Typed p (fmap f e) qty
  fmap f (Record p a c fs) = Record p (f a) c (map (fmap (fmap f)) fs)
  fmap f (RecordUpdate p e fs) = RecordUpdate p (fmap f e) (map (fmap (fmap f)) fs)
  fmap f (Tuple p es) = Tuple p (map (fmap f) es)
  fmap f (List p a es) = List p (f a) (map (fmap f) es)
  fmap f (ListCompr p e stms) = ListCompr p (fmap f e) (map (fmap f) stms)
  fmap f (EnumFrom p e) = EnumFrom p (fmap f e)
  fmap f (EnumFromThen p e1 e2) = EnumFromThen p (fmap f e1) (fmap f e2)
  fmap f (EnumFromTo p e1 e2) = EnumFromTo p (fmap f e1) (fmap f e2)
  fmap f (EnumFromThenTo p e1 e2 e3) =
    EnumFromThenTo p (fmap f e1) (fmap f e2) (fmap f e3)
  fmap f (UnaryMinus p e) = UnaryMinus p (fmap f e)
  fmap f (Apply p e1 e2) = Apply p (fmap f e1) (fmap f e2)
  fmap f (InfixApply p e1 op e2) =
    InfixApply p (fmap f e1) (fmap f op) (fmap f e2)
  fmap f (LeftSection p e op) = LeftSection p (fmap f e) (fmap f op)
  fmap f (RightSection p op e) = RightSection p (fmap f op) (fmap f e)
  fmap f (Lambda p ts e) = Lambda p (map (fmap f) ts) (fmap f e)
  fmap f (Let p li ds e) = Let p li (map (fmap f) ds) (fmap f e)
  fmap f (Do p li stms e) = Do p li (map (fmap f) stms) (fmap f e)
  fmap f (IfThenElse p e1 e2 e3) =
    IfThenElse p (fmap f e1) (fmap f e2) (fmap f e3)
  fmap f (Case p li ct e as) = Case p li ct (fmap f e) (map (fmap f) as)

instance Functor InfixOp where
  fmap f (InfixOp a op) = InfixOp (f a) op
  fmap f (InfixConstr a op) = InfixConstr (f a) op

instance Functor Statement where
  fmap f (StmtExpr p e) = StmtExpr p (fmap f e)
  fmap f (StmtDecl p li ds) = StmtDecl p li (map (fmap f) ds)
  fmap f (StmtBind p t e) = StmtBind p (fmap f t) (fmap f e)

instance Functor Alt where
  fmap f (Alt p t rhs) = Alt p (fmap f t) (fmap f rhs)

instance Functor Field where
  fmap f (Field p l x) = Field p l (f x)

instance Functor Var where
  fmap f (Var a v) = Var (f a) v

instance Functor Goal where
  fmap f (Goal p li e ds) = Goal p li (fmap f e) (map (fmap f) ds)

instance Pretty Infix where
  pPrint InfixL = text "infixl"
  pPrint InfixR = text "infixr"
  pPrint Infix  = text "infix"

instance HasSpanInfo (Module a) where
  getSpanInfo (Module sp _ _ _ _ _ _) = sp

  setSpanInfo sp (Module _ li ps m es is ds) = Module sp li ps m es is ds

  updateEndPos m@(Module _ _ _ _ _ _ (d:ds)) =
    setEndPosition (getSrcSpanEnd (last (d:ds))) m
  updateEndPos m@(Module _ _ _ _ _ (i:is) _) =
    setEndPosition (getSrcSpanEnd (last (i:is))) m
  updateEndPos m@(Module (SpanInfo _ (s:ss)) _ _ _ _ _ _) =
    setEndPosition (end (last (s:ss))) m
  updateEndPos m@(Module _ _ (p:ps) _ _ _ _) =
    setEndPosition (getSrcSpanEnd (last (p:ps))) m
  updateEndPos m = m

  getLayoutInfo (Module _ li _ _ _ _ _) = li

instance HasSpanInfo (Decl a) where
  getSpanInfo (InfixDecl        sp _ _ _)   = sp
  getSpanInfo (DataDecl         sp _ _ _ _) = sp
  getSpanInfo (ExternalDataDecl sp _ _)     = sp
  getSpanInfo (NewtypeDecl      sp _ _ _ _) = sp
  getSpanInfo (TypeDecl         sp _ _ _)   = sp
  getSpanInfo (TypeSig          sp _ _)     = sp
  getSpanInfo (FunctionDecl     sp _ _ _)   = sp
  getSpanInfo (ExternalDecl     sp _)       = sp
  getSpanInfo (PatternDecl      sp _ _)     = sp
  getSpanInfo (FreeDecl         sp _)       = sp
  getSpanInfo (DefaultDecl      sp _)       = sp
  getSpanInfo (ClassDecl        sp _ _ _ _ _) = sp
  getSpanInfo (InstanceDecl     sp _ _ _ _ _) = sp

  setSpanInfo sp (InfixDecl _ fix prec ops) = InfixDecl sp fix prec ops
  setSpanInfo sp (DataDecl _ tc tvs cs clss) = DataDecl sp tc tvs cs clss
  setSpanInfo sp (ExternalDataDecl _ tc tvs) = ExternalDataDecl sp tc tvs
  setSpanInfo sp (NewtypeDecl _ tc tvs nc clss) = NewtypeDecl sp tc tvs nc clss
  setSpanInfo sp (TypeDecl _ tc tvs ty) = TypeDecl sp tc tvs ty
  setSpanInfo sp (TypeSig _ fs qty) = TypeSig sp fs qty
  setSpanInfo sp (FunctionDecl _ a f' eqs) = FunctionDecl sp a f' eqs
  setSpanInfo sp (ExternalDecl _ vs) = ExternalDecl sp vs
  setSpanInfo sp (PatternDecl _ t rhs) = PatternDecl sp t rhs
  setSpanInfo sp (FreeDecl _ vs) = FreeDecl sp vs
  setSpanInfo sp (DefaultDecl _ tys) = DefaultDecl sp tys
  setSpanInfo sp (ClassDecl _ li cx cls clsvar ds) = ClassDecl sp li cx cls clsvar ds
  setSpanInfo sp (InstanceDecl _ li cx qcls inst ds) = InstanceDecl sp li cx qcls inst ds

  updateEndPos d@(InfixDecl _ _ _ ops) =
    let i' = last ops
    in setEndPosition (incr (getPosition i') (identLength i' - 1)) d
  updateEndPos d@(DataDecl _ _ _ _ (c:cs)) =
    let i' = last (c:cs)
    in setEndPosition (incr (getPosition i') (qIdentLength i' - 1)) d
  updateEndPos d@(DataDecl _ _ _ (c:cs) _) =
    setEndPosition (getSrcSpanEnd (last (c:cs))) d
  updateEndPos d@(DataDecl _ _ (i:is) _ _) =
    let i' = last (i:is)
    in setEndPosition (incr (getPosition i') (identLength i' - 1)) d
  updateEndPos d@(DataDecl _ i _ _ _) =
    setEndPosition (incr (getPosition i) (identLength i - 1)) d
  updateEndPos d@(ExternalDataDecl _ _ (i:is)) =
    let i' = last (i:is)
    in setEndPosition (incr (getPosition i') (identLength i' - 1)) d
  updateEndPos d@(ExternalDataDecl _ i _) =
    setEndPosition (incr (getPosition i) (identLength i - 1)) d
  updateEndPos d@(NewtypeDecl _ _ _ _ (c:cs)) =
    let i' = last (c:cs)
    in setEndPosition (incr (getPosition i') (qIdentLength i' - 1)) d
  updateEndPos d@(NewtypeDecl _ _ _ c _) =
    setEndPosition (getSrcSpanEnd c) d
  updateEndPos d@(TypeDecl _ _ _ ty) =
    setEndPosition (getSrcSpanEnd ty) d
  updateEndPos d@(TypeSig _ _ qty) =
    setEndPosition (getSrcSpanEnd qty) d
  updateEndPos d@(FunctionDecl _ _ _ eqs) =
    setEndPosition (getSrcSpanEnd (last eqs)) d
  updateEndPos d@(ExternalDecl (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) d
  updateEndPos d@(ExternalDecl _ _) = d
  updateEndPos d@(PatternDecl _ _ rhs) =
    setEndPosition (getSrcSpanEnd rhs) d
  updateEndPos d@(FreeDecl (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) d
  updateEndPos d@(FreeDecl _ _) = d
  updateEndPos d@(DefaultDecl (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) d
  updateEndPos d@(DefaultDecl _ _) = d
  updateEndPos d@(ClassDecl _ _ _ _ _ (d':ds)) =
    setEndPosition (getSrcSpanEnd (last (d':ds))) d
  updateEndPos d@(ClassDecl (SpanInfo _ ss) _ _ _ _ _) =
    setEndPosition (end (last ss)) d
  updateEndPos d@(ClassDecl _ _ _ _ _ _) = d
  updateEndPos d@(InstanceDecl _ _ _ _ _ (d':ds)) =
    setEndPosition (getSrcSpanEnd (last (d':ds))) d
  updateEndPos d@(InstanceDecl (SpanInfo _ ss) _ _ _ _ _) =
    setEndPosition (end (last ss)) d
  updateEndPos d@(InstanceDecl _ _ _ _ _ _) = d

  getLayoutInfo (ClassDecl _ li _ _ _ _) = li
  getLayoutInfo (InstanceDecl _ li _ _ _ _) = li
  getLayoutInfo _ = WhitespaceLayout

instance HasSpanInfo (Equation a) where
  getSpanInfo (Equation spi _ _) = spi
  setSpanInfo spi (Equation _ lhs rhs) = Equation spi lhs rhs
  updateEndPos e@(Equation _ _ rhs) =
    setEndPosition (getSrcSpanEnd rhs) e

instance HasSpanInfo ModulePragma where
  getSpanInfo (LanguagePragma sp _  ) = sp
  getSpanInfo (OptionsPragma  sp _ _) = sp

  setSpanInfo sp (LanguagePragma _ ex ) = LanguagePragma sp ex
  setSpanInfo sp (OptionsPragma  _ t a) = OptionsPragma sp t a

  updateEndPos p@(LanguagePragma (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) p
  updateEndPos p@(LanguagePragma _ _) = p
  updateEndPos p@(OptionsPragma (SpanInfo _ ss) _ _) =
    setEndPosition (end (last ss)) p
  updateEndPos p@(OptionsPragma _ _ _) = p

instance HasSpanInfo ExportSpec where
  getSpanInfo (Exporting sp _) = sp
  setSpanInfo sp (Exporting _ ex) = Exporting sp ex

  updateEndPos e@(Exporting (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) e
  updateEndPos e@(Exporting _ _) = e

instance HasSpanInfo Export where
  getSpanInfo (Export sp _)           = sp
  getSpanInfo (ExportTypeWith sp _ _) = sp
  getSpanInfo (ExportTypeAll sp _)    = sp
  getSpanInfo (ExportModule sp _)     = sp

  setSpanInfo sp (Export _ qid)            = Export sp qid
  setSpanInfo sp (ExportTypeWith _ qid cs) = ExportTypeWith sp qid cs
  setSpanInfo sp (ExportTypeAll _ qid)     = ExportTypeAll sp qid
  setSpanInfo sp (ExportModule _ mid)      = ExportModule sp mid

  updateEndPos e@(Export _ idt) =
    setEndPosition (incr (getPosition idt) (qIdentLength idt - 1)) e
  updateEndPos e@(ExportTypeWith (SpanInfo _ ss) _ _) =
    setEndPosition (end (last ss)) e
  updateEndPos e@(ExportTypeWith _ _ _) = e
  updateEndPos e@(ExportTypeAll (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) e
  updateEndPos e@(ExportTypeAll _ _) = e
  updateEndPos e@(ExportModule _ mid) =
    setEndPosition (incr (getPosition mid) (mIdentLength mid - 1)) e

instance HasSpanInfo ImportDecl where
  getSpanInfo (ImportDecl sp _ _ _ _) = sp
  setSpanInfo sp (ImportDecl _ mid q as spec) = ImportDecl sp mid q as spec

  updateEndPos i@(ImportDecl _ _ _ _ (Just spec)) =
    setEndPosition (getSrcSpanEnd spec) i
  updateEndPos i@(ImportDecl _ _ _ (Just mid) _) =
    setEndPosition (incr (getPosition mid) (mIdentLength mid - 1)) i
  updateEndPos i@(ImportDecl _ mid _ _ _) =
    setEndPosition (incr (getPosition mid) (mIdentLength mid - 1)) i

instance HasSpanInfo ImportSpec where
  getSpanInfo (Importing sp _) = sp
  getSpanInfo (Hiding    sp _) = sp

  setSpanInfo sp (Importing _ im) = Importing sp im
  setSpanInfo sp (Hiding    _ im) = Hiding sp im

  updateEndPos i@(Importing (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) i
  updateEndPos i@(Importing _ _) = i
  updateEndPos i@(Hiding (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) i
  updateEndPos i@(Hiding _ _) = i

instance HasSpanInfo Import where
  getSpanInfo (Import sp _)           = sp
  getSpanInfo (ImportTypeWith sp _ _) = sp
  getSpanInfo (ImportTypeAll sp _)    = sp

  setSpanInfo sp (Import _ qid)            = Import sp qid
  setSpanInfo sp (ImportTypeWith _ qid cs) = ImportTypeWith sp qid cs
  setSpanInfo sp (ImportTypeAll _ qid)     = ImportTypeAll sp qid

  updateEndPos i@(Import _ idt) =
    setEndPosition (incr (getPosition idt) (identLength idt - 1)) i
  updateEndPos i@(ImportTypeWith (SpanInfo _ ss) _ _) =
    setEndPosition (end (last ss)) i
  updateEndPos i@(ImportTypeWith _ _ _) = i
  updateEndPos i@(ImportTypeAll (SpanInfo _ ss) _) =
    setEndPosition (end (last ss)) i
  updateEndPos i@(ImportTypeAll _ _) = i

instance HasSpanInfo ConstrDecl where
  getSpanInfo (ConstrDecl sp _ _)   = sp
  getSpanInfo (ConOpDecl  sp _ _ _) = sp
  getSpanInfo (RecordDecl sp _ _)   = sp

  setSpanInfo sp (ConstrDecl _ idt ty) = ConstrDecl sp idt ty
  setSpanInfo sp (ConOpDecl  _ ty1 idt ty2) = ConOpDecl sp ty1 idt ty2
  setSpanInfo sp (RecordDecl _ idt fd) = RecordDecl sp idt fd

  updateEndPos c@(ConstrDecl _ _ (t:ts)) =
    setEndPosition (getSrcSpanEnd (last (t:ts))) c
  updateEndPos c@(ConstrDecl _ idt _) =
    setEndPosition (incr (getPosition idt) (identLength idt - 1)) c
  updateEndPos c@(ConOpDecl _ _ _ ty) =
    setEndPosition (getSrcSpanEnd ty) c
  updateEndPos c@(RecordDecl (SpanInfo _ ss) _ _) =
    setEndPosition (end (last ss)) c
  updateEndPos c@(RecordDecl _ _ _) = c

instance HasSpanInfo NewConstrDecl where
  getSpanInfo (NewConstrDecl sp _ _)   = sp
  getSpanInfo (NewRecordDecl sp _ _)   = sp

  setSpanInfo sp (NewConstrDecl _ idt ty)  = NewConstrDecl sp idt ty
  setSpanInfo sp (NewRecordDecl _ idt fty) = NewRecordDecl sp idt fty

  updateEndPos c@(NewConstrDecl _ _ ty) =
    setEndPosition (getSrcSpanEnd ty) c
  updateEndPos c@(NewRecordDecl (SpanInfo _ ss) _ _) =
    setEndPosition (end (last ss)) c
  updateEndPos c@(NewRecordDecl _ _ _) = c

instance HasSpanInfo FieldDecl where
    getSpanInfo (FieldDecl sp _ _) = sp
    setSpanInfo sp (FieldDecl _ idt ty) = FieldDecl sp idt ty
    updateEndPos d@(FieldDecl _ _ ty) =
      setEndPosition (getSrcSpanEnd ty) d

instance HasSpanInfo TypeExpr where
  getSpanInfo (ConstructorType sp _) = sp
  getSpanInfo (ApplyType sp _ _)     = sp
  getSpanInfo (VariableType sp _)    = sp
  getSpanInfo (TupleType sp _)       = sp
  getSpanInfo (ListType sp _)        = sp
  getSpanInfo (ArrowType sp _ _)     = sp
  getSpanInfo (ParenType sp _)       = sp
  getSpanInfo (ForallType sp _ _)    = sp

  setSpanInfo sp (ConstructorType _ qid) = ConstructorType sp qid
  setSpanInfo sp (ApplyType _ ty1 ty2)   = ApplyType sp ty1 ty2
  setSpanInfo sp (VariableType _ idt)    = VariableType sp idt
  setSpanInfo sp (TupleType _ tys)       = TupleType sp tys
  setSpanInfo sp (ListType _ ty)         = ListType sp ty
  setSpanInfo sp (ArrowType _ ty1 ty2)   = ArrowType sp ty1 ty2
  setSpanInfo sp (ParenType _ ty)        = ParenType sp ty
  setSpanInfo sp (ForallType _ idt ty)   = ForallType sp idt ty

  updateEndPos t@(ConstructorType _ qid) =
    setEndPosition (incr (getPosition qid) (qIdentLength qid - 1)) t
  updateEndPos t@(ApplyType _ _ t2) =
    setEndPosition (getSrcSpanEnd t2) t
  updateEndPos t@(VariableType _ idt) =
    setEndPosition (incr (getPosition idt) (identLength idt - 1)) t
  updateEndPos t@(ListType (SpanInfo _ (s:ss)) _) =
    setEndPosition (end (last (s:ss))) t
  updateEndPos t@(ListType _ _) = t
  updateEndPos t@(TupleType _ tys) =
    setEndPosition (getSrcSpanEnd (last tys)) t
  updateEndPos t@(ArrowType _ _ t2) =
    setEndPosition (getSrcSpanEnd t2) t
  updateEndPos t@(ParenType (SpanInfo _ (s:ss)) _) =
    setEndPosition (end (last (s:ss))) t
  updateEndPos t@(ParenType _ _) = t
  updateEndPos t@(ForallType _ _ _) = t -- not a parseable type

instance HasSpanInfo QualTypeExpr where
  getSpanInfo (QualTypeExpr sp _ _) = sp
  setSpanInfo sp (QualTypeExpr _ cx ty) = QualTypeExpr sp cx ty
  updateEndPos t@(QualTypeExpr _ _ ty) =
    setEndPosition (getSrcSpanEnd ty) t

instance HasSpanInfo Constraint where
  getSpanInfo (Constraint sp _ _) = sp
  setSpanInfo sp (Constraint _ qid ty) = Constraint sp qid ty
  updateEndPos c@(Constraint (SpanInfo _ (s:ss)) _ _) =
    setEndPosition (end (last (s:ss))) c
  updateEndPos c@(Constraint _ _ ty) =
    setEndPosition (getSrcSpanEnd ty) c

instance HasSpanInfo (Lhs a) where
  getSpanInfo (FunLhs sp _ _)   = sp
  getSpanInfo (OpLhs  sp _ _ _) = sp
  getSpanInfo (ApLhs  sp _ _)   = sp

  setSpanInfo sp (FunLhs _ idt ps)    = FunLhs sp idt ps
  setSpanInfo sp (OpLhs  _ p1 idt p2) = OpLhs sp p1 idt p2
  setSpanInfo sp (ApLhs  _ lhs ps)    = ApLhs sp lhs ps

  updateEndPos l@(FunLhs _ _ (p:ps)) =
    setEndPosition (getSrcSpanEnd (last (p:ps))) l
  updateEndPos l@(FunLhs _ idt _) =
    setEndPosition (incr (getPosition idt) (identLength idt - 1)) l
  updateEndPos l@(OpLhs _ _ _ p) =
    setEndPosition (getSrcSpanEnd p) l
  updateEndPos l@(ApLhs _ _ (p:ps)) =
    setEndPosition (getSrcSpanEnd (last (p:ps))) l
  updateEndPos l@(ApLhs (SpanInfo _ [_,s]) _ _) =
    setEndPosition (end s) l
  updateEndPos l@(ApLhs _ _ _) = l


instance HasSpanInfo (Rhs a) where
  getSpanInfo (SimpleRhs sp _ _ _)  = sp
  getSpanInfo (GuardedRhs sp _ _ _) = sp

  setSpanInfo sp (SimpleRhs _ li ex ds)  = SimpleRhs sp li ex ds
  setSpanInfo sp (GuardedRhs _ li cs ds) = GuardedRhs sp li cs ds

  updateEndPos r@(SimpleRhs (SpanInfo _ [_,_]) _ _ (d:ds)) =
    setEndPosition (getSrcSpanEnd (last (d:ds))) r
  updateEndPos r@(SimpleRhs (SpanInfo _ [_,s]) _ _ _) =
    setEndPosition (end s) r
  updateEndPos r@(SimpleRhs _ _ e _) =
    setEndPosition (getSrcSpanEnd e) r
  updateEndPos r@(GuardedRhs (SpanInfo _ [_,_]) _ _ (d:ds)) =
    setEndPosition (getSrcSpanEnd (last (d:ds))) r
  updateEndPos r@(GuardedRhs (SpanInfo _ [_,s]) _ _ _) =
    setEndPosition (end s) r
  updateEndPos r@(GuardedRhs _ _ cs _) =
    setEndPosition (getSrcSpanEnd (last cs)) r

  getLayoutInfo (SimpleRhs _ li _ _) = li
  getLayoutInfo (GuardedRhs _ li _ _) = li

instance HasSpanInfo (CondExpr a) where
  getSpanInfo (CondExpr sp _ _) = sp
  setSpanInfo sp (CondExpr _ e1 e2) = CondExpr sp e1 e2
  updateEndPos ce@(CondExpr _ _ e) =
    setEndPosition (getSrcSpanEnd e) ce

instance HasSpanInfo (Pattern a) where
  getSpanInfo (LiteralPattern  sp _ _)      = sp
  getSpanInfo (NegativePattern sp _ _)      = sp
  getSpanInfo (VariablePattern sp _ _)      = sp
  getSpanInfo (ConstructorPattern sp _ _ _) = sp
  getSpanInfo (InfixPattern sp _ _ _ _)     = sp
  getSpanInfo (ParenPattern sp _)           = sp
  getSpanInfo (RecordPattern sp _ _ _)      = sp
  getSpanInfo (TuplePattern sp _)           = sp
  getSpanInfo (ListPattern sp _ _)          = sp
  getSpanInfo (AsPattern sp _ _)            = sp
  getSpanInfo (LazyPattern sp _)            = sp
  getSpanInfo (FunctionPattern sp _ _ _)    = sp
  getSpanInfo (InfixFuncPattern sp _ _ _ _) = sp

  setSpanInfo sp (LiteralPattern _ a l) = LiteralPattern sp a l
  setSpanInfo sp (NegativePattern _ a l) = NegativePattern sp a l
  setSpanInfo sp (VariablePattern _ a v) = VariablePattern sp a v
  setSpanInfo sp (ConstructorPattern _ a c ts) = ConstructorPattern sp a c ts
  setSpanInfo sp (InfixPattern _ a t1 op t2) = InfixPattern sp a t1 op t2
  setSpanInfo sp (ParenPattern _ t) = ParenPattern sp t
  setSpanInfo sp (RecordPattern _ a c fs) = RecordPattern sp a c fs
  setSpanInfo sp (TuplePattern _ ts) = TuplePattern sp ts
  setSpanInfo sp (ListPattern _ a ts) = ListPattern sp a ts
  setSpanInfo sp (AsPattern _ v t) = AsPattern sp v t
  setSpanInfo sp (LazyPattern _ t) = LazyPattern sp t
  setSpanInfo sp (FunctionPattern _ a f' ts) = FunctionPattern sp a f' ts
  setSpanInfo sp (InfixFuncPattern _ a t1 op t2) = InfixFuncPattern sp a t1 op t2

  updateEndPos p@(LiteralPattern  _ _ _) = p
  updateEndPos p@(NegativePattern _ _ _) = p
  updateEndPos p@(VariablePattern _ _ v) =
    setEndPosition (incr (getPosition v) (identLength v - 1)) p
  updateEndPos p@(ConstructorPattern _ _ _ (t:ts)) =
    setEndPosition (getSrcSpanEnd (last (t:ts))) p
  updateEndPos p@(ConstructorPattern _ _ c _) =
    setEndPosition (incr (getPosition c) (qIdentLength c - 1)) p
  updateEndPos p@(InfixPattern _ _ _ _ t2) =
    setEndPosition (getSrcSpanEnd t2) p
  updateEndPos p@(ParenPattern (SpanInfo _ (s:ss)) _) =
    setEndPosition (end (last (s:ss))) p
  updateEndPos p@(ParenPattern _ _) = p
  updateEndPos p@(RecordPattern (SpanInfo _ (s:ss)) _ _ _) =
    setEndPosition (end (last (s:ss))) p
  updateEndPos p@(RecordPattern _ _ _ _) = p
  updateEndPos p@(TuplePattern (SpanInfo _ (s:ss)) _) =
    setEndPosition (end (last (s:ss))) p
  updateEndPos p@(TuplePattern _ _) = p
  updateEndPos p@(ListPattern (SpanInfo _ (s:ss)) _ _) =
    setEndPosition (end (last (s:ss))) p
  updateEndPos p@(ListPattern _ _ _) = p
  updateEndPos p@(AsPattern _ _ t) =
    setEndPosition (getSrcSpanEnd t) p
  updateEndPos p@(LazyPattern _ t) =
    setEndPosition (getSrcSpanEnd t) p
  updateEndPos p@(FunctionPattern _ _ _ _) = p
  updateEndPos p@(InfixFuncPattern _ _ _ _ _) = p

instance HasSpanInfo (Expression a) where
  getSpanInfo (Literal sp _ _) = sp
  getSpanInfo (Variable sp _ _) = sp
  getSpanInfo (Constructor sp _ _) = sp
  getSpanInfo (Paren sp _) = sp
  getSpanInfo (Typed sp _ _) = sp
  getSpanInfo (Record sp _ _ _) = sp
  getSpanInfo (RecordUpdate sp _ _) = sp
  getSpanInfo (Tuple sp _) = sp
  getSpanInfo (List sp _ _) = sp
  getSpanInfo (ListCompr sp _ _) = sp
  getSpanInfo (EnumFrom sp _) = sp
  getSpanInfo (EnumFromThen sp _ _) = sp
  getSpanInfo (EnumFromTo sp _ _) = sp
  getSpanInfo (EnumFromThenTo sp _ _ _) = sp
  getSpanInfo (UnaryMinus sp _) = sp
  getSpanInfo (Apply sp _ _) = sp
  getSpanInfo (InfixApply sp _ _ _) = sp
  getSpanInfo (LeftSection sp _ _) = sp
  getSpanInfo (RightSection sp _ _) = sp
  getSpanInfo (Lambda sp _ _) = sp
  getSpanInfo (Let sp _ _ _) = sp
  getSpanInfo (Do sp _ _ _) = sp
  getSpanInfo (IfThenElse sp _ _ _) = sp
  getSpanInfo (Case sp _ _ _ _) = sp

  setSpanInfo sp (Literal _ a l) = Literal sp a l
  setSpanInfo sp (Variable _ a v) = Variable sp a v
  setSpanInfo sp (Constructor _ a c) = Constructor sp a c
  setSpanInfo sp (Paren _ e) = Paren sp e
  setSpanInfo sp (Typed _ e qty) = Typed sp e qty
  setSpanInfo sp (Record _ a c fs) = Record sp a c fs
  setSpanInfo sp (RecordUpdate _ e fs) = RecordUpdate sp e fs
  setSpanInfo sp (Tuple _ es) = Tuple sp es
  setSpanInfo sp (List _ a es) = List sp a es
  setSpanInfo sp (ListCompr _ e stms) = ListCompr sp e stms
  setSpanInfo sp (EnumFrom _ e) = EnumFrom sp e
  setSpanInfo sp (EnumFromThen _ e1 e2) = EnumFromThen sp e1 e2
  setSpanInfo sp (EnumFromTo _ e1 e2) = EnumFromTo sp e1 e2
  setSpanInfo sp (EnumFromThenTo _ e1 e2 e3) = EnumFromThenTo sp e1 e2 e3
  setSpanInfo sp (UnaryMinus _ e) = UnaryMinus sp e
  setSpanInfo sp (Apply _ e1 e2) = Apply sp e1 e2
  setSpanInfo sp (InfixApply _ e1 op e2) = InfixApply sp e1 op e2
  setSpanInfo sp (LeftSection _ e op) = LeftSection sp e op
  setSpanInfo sp (RightSection _ op e) = RightSection sp op e
  setSpanInfo sp (Lambda _ ts e) = Lambda sp ts e
  setSpanInfo sp (Let _ li ds e) = Let sp li ds e
  setSpanInfo sp (Do _ li stms e) = Do sp li stms e
  setSpanInfo sp (IfThenElse _ e1 e2 e3) = IfThenElse sp e1 e2 e3
  setSpanInfo sp (Case _ li ct e as) = Case sp li ct e as

  updateEndPos e@(Literal _ _ _) = e
  updateEndPos e@(Variable _ _ v) =
    setEndPosition (incr (getPosition v) (qIdentLength v - 1)) e
  updateEndPos e@(Constructor _ _ c) =
    setEndPosition (incr (getPosition c) (qIdentLength c - 1)) e
  updateEndPos e@(Paren (SpanInfo _ [_,s]) _) =
    setEndPosition (end s) e
  updateEndPos e@(Paren _ _) = e
  updateEndPos e@(Typed _ _ qty) =
    setEndPosition (getSrcSpanEnd qty) e
  updateEndPos e@(Record (SpanInfo _ (s:ss)) _ _ _) =
    setEndPosition (end (last (s:ss))) e
  updateEndPos e@(Record _ _ _ _) = e
  updateEndPos e@(RecordUpdate (SpanInfo _ (s:ss)) _ _) =
    setEndPosition (end (last (s:ss))) e
  updateEndPos e@(RecordUpdate _ _ _) = e
  updateEndPos e@(Tuple (SpanInfo _ [_,s]) _) =
    setEndPosition (end s) e
  updateEndPos e@(Tuple _ _) = e
  updateEndPos e@(List (SpanInfo _ (s:ss)) _ _) =
    setEndPosition (end (last (s:ss))) e
  updateEndPos e@(List _ _ _) = e
  updateEndPos e@(ListCompr (SpanInfo _ (s:ss)) _ _) =
    setEndPosition (end (last (s:ss))) e
  updateEndPos e@(ListCompr _ _ _) = e
  updateEndPos e@(EnumFrom (SpanInfo _ [_,_,s]) _) =
    setEndPosition (end s) e
  updateEndPos e@(EnumFrom _ _) = e
  updateEndPos e@(EnumFromTo (SpanInfo _ [_,_,s]) _ _) =
    setEndPosition (end s) e
  updateEndPos e@(EnumFromTo _ _ _) = e
  updateEndPos e@(EnumFromThen (SpanInfo _ [_,_,_,s]) _ _) =
    setEndPosition (end s) e
  updateEndPos e@(EnumFromThen _ _ _) = e
  updateEndPos e@(EnumFromThenTo (SpanInfo _ [_,_,_,s]) _ _ _) =
    setEndPosition (end s) e
  updateEndPos e@(EnumFromThenTo _ _ _ _) = e
  updateEndPos e@(UnaryMinus _ e') =
    setEndPosition (getSrcSpanEnd e') e
  updateEndPos e@(Apply _ _ e') =
    setEndPosition (getSrcSpanEnd e') e
  updateEndPos e@(InfixApply _ _ _ e') =
    setEndPosition (getSrcSpanEnd e') e
  updateEndPos e@(LeftSection (SpanInfo _ [_,s]) _ _) =
    setEndPosition (end s) e
  updateEndPos e@(LeftSection _ _ _) = e
  updateEndPos e@(RightSection (SpanInfo _ [_,s]) _ _) =
    setEndPosition (end s) e
  updateEndPos e@(RightSection _ _ _) = e
  updateEndPos e@(Lambda _ _ e') =
    setEndPosition (getSrcSpanEnd e') e
  updateEndPos e@(Let _ _ _ e') =
    setEndPosition (getSrcSpanEnd e') e
  updateEndPos e@(Do _ _ _ e') =
    setEndPosition (getSrcSpanEnd e') e
  updateEndPos e@(IfThenElse _ _ _ e') =
    setEndPosition (getSrcSpanEnd e') e
  updateEndPos e@(Case _ _ _ _ (a:as)) =
    setEndPosition (getSrcSpanEnd (last (a:as))) e
  updateEndPos e@(Case (SpanInfo _ (s:ss)) _ _ _ _) =
    setEndPosition (end (last (s:ss))) e
  updateEndPos e@(Case _ _ _ _ _) = e

  getLayoutInfo (Let _ li _ _) = li
  getLayoutInfo (Do _ li _ _) = li
  getLayoutInfo (Case _ li _ _ _) = li
  getLayoutInfo _ = WhitespaceLayout

instance HasSpanInfo (Statement a) where
  getSpanInfo (StmtExpr sp _)   = sp
  getSpanInfo (StmtDecl sp _ _) = sp
  getSpanInfo (StmtBind sp _ _) = sp

  setSpanInfo sp (StmtExpr _    ex) = StmtExpr sp ex
  setSpanInfo sp (StmtDecl _ li ds) = StmtDecl sp li ds
  setSpanInfo sp (StmtBind _ p  ex) = StmtBind sp p ex

  updateEndPos s@(StmtExpr _ e) =
    setEndPosition (getSrcSpanEnd e) s
  updateEndPos s@(StmtBind _ _ e) =
    setEndPosition (getSrcSpanEnd e) s
  updateEndPos s@(StmtDecl _ _ (d:ds)) =
    setEndPosition (getSrcSpanEnd (last (d:ds))) s
  updateEndPos s@(StmtDecl (SpanInfo _ [s']) _ _) = -- empty let
    setEndPosition (end s') s
  updateEndPos s@(StmtDecl _ _ _) = s

  getLayoutInfo (StmtDecl _ li _) = li
  getLayoutInfo _ = WhitespaceLayout

instance HasSpanInfo (Alt a) where
  getSpanInfo (Alt sp _ _) = sp
  setSpanInfo sp (Alt _ p rhs) = Alt sp p rhs
  updateEndPos a@(Alt _ _ rhs) =
    setEndPosition (getSrcSpanEnd rhs) a

instance HasSpanInfo (Field a) where
  getSpanInfo (Field sp _ _) = sp
  setSpanInfo sp (Field _ qid a) = Field sp qid a
  updateEndPos f@(Field (SpanInfo _ ss) _ _) =
    setEndPosition (end (last ss)) f
  updateEndPos f@(Field _ _ _) = f

instance HasSpanInfo (Goal a) where
  getSpanInfo (Goal sp _ _ _) = sp
  setSpanInfo sp (Goal _ li e ds) = Goal sp li e ds

  updateEndPos g@(Goal (SpanInfo _ [_]) _ _ (d:ds)) =
    setEndPosition (getSrcSpanEnd (last (d:ds))) g
  updateEndPos g@(Goal (SpanInfo _ [s]) _ _ _) =
    setEndPosition (end s) g
  updateEndPos g@(Goal _ _ _ _) = g

  getLayoutInfo (Goal _ li _ _) = li

instance HasPosition (Module a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Decl a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Equation a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition ModulePragma where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition ExportSpec where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition ImportDecl where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition ImportSpec where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition Export where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition Import where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition ConstrDecl where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition TypeExpr where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition QualTypeExpr where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition NewConstrDecl where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition Constraint where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition FieldDecl where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Lhs a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Rhs a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (CondExpr a) where
  getPosition = getStartPosition

instance HasPosition (Pattern a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Expression a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Alt a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Goal a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Field a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (Statement a) where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasPosition (InfixOp a) where
  getPosition (InfixOp     _ q) = getPosition q
  getPosition (InfixConstr _ q) = getPosition q

  setPosition p (InfixOp     a q) = InfixOp     a (setPosition p q)
  setPosition p (InfixConstr a q) = InfixConstr a (setPosition p q)

{- HLINT ignore "Use record patterns"-}
