{- |
    Module      : $Header$
    Description : Representation of FlatCurry.
    Copyright   : (c) Michael Hanus  2003
                      Martin Engelke 2004
                      Bernd Brassel  2005
    License     : BSD-3-clause

    Maintainer  : bjp@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This module contains a definition for representing FlatCurry programs
    in Haskell in type 'Prog'.
-}

module Curry.FlatCurry.Type
  ( -- * Representation of qualified names and (type) variables
    QName, VarIndex, TVarIndex, TVarWithKind
    -- * Data types for FlatCurry
  , Visibility (..), Prog (..), TypeDecl (..), TypeExpr (..), Kind (..)
  , ConsDecl (..), NewConsDecl(..), OpDecl (..), Fixity (..)
  , FuncDecl (..), Rule (..), Expr (..), Literal (..)
  , CombType (..), CaseType (..), BranchExpr (..), Pattern (..)
  ) where

import Data.Binary
import Control.Monad

-- ---------------------------------------------------------------------------
-- Qualified names
-- ---------------------------------------------------------------------------

-- |Qualified names.
--
-- In FlatCurry all names are qualified to avoid name clashes.
-- The first component is the module name and the second component the
-- unqualified name as it occurs in the source program.
type QName = (String, String)

-- ---------------------------------------------------------------------------
-- Variable representation
-- ---------------------------------------------------------------------------

-- |Representation of variables.
type VarIndex = Int

-- ---------------------------------------------------------------------------
-- FlatCurry representation
-- ---------------------------------------------------------------------------

-- |Visibility of various entities.
data Visibility
  = Public    -- ^ public (exported) entity
  | Private   -- ^ private entity
    deriving (Eq, Read, Show)

-- |A FlatCurry module.
--
-- A value of this data type has the form
--
-- @Prog modname imports typedecls functions opdecls@
--
-- where
--
-- [@modname@]   Name of this module
-- [@imports@]   List of modules names that are imported
-- [@typedecls@] Type declarations
-- [@funcdecls@] Function declarations
-- [@ opdecls@]  Operator declarations
data Prog = Prog String [String] [TypeDecl] [FuncDecl] [OpDecl]
    deriving (Eq, Read, Show)

-- |Declaration of algebraic data type or type synonym.
--
-- A data type declaration of the form
--
-- @data t x1...xn = ...| c t1....tkc |...@
--
-- is represented by the FlatCurry term
--
-- @Type t [i1,...,in] [...(Cons c kc [t1,...,tkc])...]@
--
-- where each @ij@ is the index of the type variable @xj@
--
-- /Note:/ The type variable indices are unique inside each type declaration
--         and are usually numbered from 0.
--
-- Thus, a data type declaration consists of the name of the data type,
-- a list of type parameters and a list of constructor declarations.
data TypeDecl
  = Type    QName Visibility [TVarWithKind] [ConsDecl]
  | TypeSyn QName Visibility [TVarWithKind] TypeExpr
  | TypeNew QName Visibility [TVarWithKind] NewConsDecl
    deriving (Eq, Read, Show)

-- |Type variables are represented by @(TVar i)@ where @i@ is a
-- type variable index.
type TVarIndex = Int

-- |Kinded type variables are represented by a tuple of type variable
-- index and kind.
type TVarWithKind = (TVarIndex, Kind)

-- |A constructor declaration consists of the name and arity of the
-- constructor and a list of the argument types of the constructor.
data ConsDecl = Cons QName Int Visibility [TypeExpr]
    deriving (Eq, Read, Show)

-- |A constructor declaration for a newtype consists
-- of the name of the constructor
-- and the argument type of the constructor.
data NewConsDecl = NewCons QName Visibility TypeExpr
    deriving (Eq, Read, Show)

-- |Type expressions.
--
-- A type expression is either a type variable, a function type,
-- or a type constructor application.
--
-- /Note:/ the names of the predefined type constructors are
-- @Int@, @Float@, @Bool@, @Char@, @IO@, @Success@,
-- @()@ (unit type), @(,...,)@ (tuple types), @[]@ (list type)
data TypeExpr
  = TVar        TVarIndex               -- ^ type variable
  | FuncType    TypeExpr TypeExpr       -- ^ function type @t1 -> t2@
  | TCons QName [TypeExpr]              -- ^ type constructor application
  | ForallType  [TVarWithKind] TypeExpr -- ^ forall type
    deriving (Eq, Read, Show)

-- |Kinds.
--
-- A kind is either * or k_1 -> k_2 where k_1 and k_2 are kinds.
data Kind
  = KStar            -- ^ star kind
  | KArrow Kind Kind -- ^ arrow kind
 deriving (Eq, Ord, Read, Show)
    
-- |Operator declarations.
--
-- An operator declaration @fix p n@ in Curry corresponds to the
-- FlatCurry term @(Op n fix p)@.
--
-- /Note:/ the constructor definition of 'Op' differs from the original
-- PAKCS definition using Haskell type 'Integer' instead of 'Int'
-- for representing the precedence.
data OpDecl = Op QName Fixity Integer
    deriving (Eq, Read, Show)

-- |Fixity of an operator.
data Fixity
  = InfixOp  -- ^ non-associative infix operator
  | InfixlOp -- ^ left-associative infix operator
  | InfixrOp -- ^ right-associative infix operator
    deriving (Eq, Read, Show)

-- |Data type for representing function declarations.
--
-- A function declaration in FlatCurry is a term of the form
--
-- @(Func name arity type (Rule [i_1,...,i_arity] e))@
--
-- and represents the function "name" with definition
--
-- @
-- name :: type
-- name x_1...x_arity = e
-- @
--
-- where each @i_j@ is the index of the variable @x_j@
--
-- /Note:/ The variable indices are unique inside each function declaration
--         and are usually numbered from 0.
--
-- External functions are represented as
--
-- @Func name arity type (External s)@
--
-- where s is the external name associated to this function.
--
-- Thus, a function declaration consists of the name, arity, type, and rule.
data FuncDecl = Func QName Int Visibility TypeExpr Rule
    deriving (Eq, Read, Show)

-- |A rule is either a list of formal parameters together with an expression
-- or an 'External' tag.
data Rule
  = Rule [VarIndex] Expr
  | External String
    deriving (Eq, Read, Show)

-- |Data type for representing expressions.
--
-- Remarks:
--
-- 1.if-then-else expressions are represented as function calls:
--
--   @(if e1 then e2 else e3)@
--
--   is represented as
--
--   @(Comb FuncCall ("Prelude","ifThenElse") [e1,e2,e3])@
--
-- 2.Higher order applications are represented as calls to the (external)
--   function @apply@. For instance, the rule
--
--   @app f x = f x@
--
--   is represented as
--
--   @(Rule  [0,1] (Comb FuncCall ("Prelude","apply") [Var 0, Var 1]))@
--
-- 3.A conditional rule is represented as a call to an external function
--   @cond@ where the first argument is the condition (a constraint).
--
--   For instance, the rule
--
--   @equal2 x | x=:=2 = success@
--
--   is represented as
--
--   @
--   (Rule [0]
--       (Comb FuncCall ("Prelude","cond")
--             [Comb FuncCall ("Prelude","=:=") [Var 0, Lit (Intc 2)],
--             Comb FuncCall ("Prelude","success") []]))
--   @
--
-- 4.Functions with evaluation annotation @choice@ are represented
--   by a rule whose right-hand side is enclosed in a call to the
--   external function @Prelude.commit@.
--   Furthermore, all rules of the original definition must be
--   represented by conditional expressions (i.e., (cond [c,e]))
--   after pattern matching.
--
--   Example:
--
--   @
--   m eval choice
--   m [] y = y
--   m x [] = x
--   @
--
--   is translated into (note that the conditional branches can be also
--   wrapped with Free declarations in general):
--
--   @
--   Rule [0,1]
--     (Comb FuncCall ("Prelude","commit")
--       [Or (Case Rigid (Var 0)
--             [(Pattern ("Prelude","[]") []
--                 (Comb FuncCall ("Prelude","cond")
--                       [Comb FuncCall ("Prelude","success") [],
--                         Var 1]))] )
--           (Case Rigid (Var 1)
--             [(Pattern ("Prelude","[]") []
--                 (Comb FuncCall ("Prelude","cond")
--                       [Comb FuncCall ("Prelude","success") [],
--                         Var 0]))] )])
--   @
--
--   Operational meaning of @(Prelude.commit e)@:
--   evaluate @e@ with local search spaces and commit to the first
--   @(Comb FuncCall ("Prelude","cond") [c,ge])@ in @e@ whose constraint @c@
--   is satisfied
data Expr
  -- |Variable, represented by unique index
  = Var VarIndex
  -- |Literal (Integer/Float/Char constant)
  | Lit Literal
  -- |Application @(f e1 ... en)@ of function/constructor @f@
  --  with @n <= arity f@
  | Comb CombType QName [Expr]
  -- |Introduction of free local variables for an expression
  | Free [VarIndex] Expr
  -- |Local let-declarations
  | Let [(VarIndex, Expr)] Expr
  -- |Disjunction of two expressions
  -- (resulting from overlapping left-hand sides)
  | Or Expr Expr
  -- |case expression
  | Case CaseType Expr [BranchExpr]
  -- |typed expression
  | Typed Expr TypeExpr
    deriving (Eq, Read, Show)

-- |Data type for representing literals.
--
-- A literal  is either an integer, a float, or a character constant.
--
-- /Note:/ The constructor definition of 'Intc' differs from the original
-- PAKCS definition. It uses Haskell type 'Integer' instead of 'Int'
-- to provide an unlimited range of integer numbers. Furthermore,
-- float values are represented with Haskell type 'Double' instead of
-- 'Float'.
data Literal
  = Intc   Integer
  | Floatc Double
  | Charc  Char
    deriving (Eq, Read, Show)

-- |Data type for classifying combinations
-- (i.e., a function/constructor applied to some arguments).
data CombType
  -- |a call to a function where all arguments are provided
  = FuncCall
  -- |a call with a constructor at the top, all arguments are provided
  | ConsCall
  -- |a partial call to a function (i.e., not all arguments are provided)
  --  where the parameter is the number of missing arguments
  | FuncPartCall Int
  -- |a partial call to a constructor along with number of missing arguments
  | ConsPartCall Int
    deriving (Eq, Read, Show)

-- |Classification of case expressions, either flexible or rigid.
data CaseType
  = Rigid
  | Flex
    deriving (Eq, Read, Show)

-- |Branches in a case expression.
--
-- Branches @(m.c x1...xn) -> e@ in case expressions are represented as
--
-- @(Branch (Pattern (m,c) [i1,...,in]) e)@
--
-- where each @ij@ is the index of the pattern variable @xj@, or as
--
-- @(Branch (LPattern (Intc i)) e)@
--
-- for integers as branch patterns (similarly for other literals
-- like float or character constants).
data BranchExpr = Branch Pattern Expr
    deriving (Eq, Read, Show)

-- |Patterns in case expressions.
data Pattern
  = Pattern QName [VarIndex]
  | LPattern Literal
    deriving (Eq, Read, Show)

instance Binary Visibility where
  put Public  = putWord8 0
  put Private = putWord8 1

  get = do
    x <- getWord8
    case x of
      0 -> return Public
      1 -> return Private
      _ -> fail "Invalid encoding for Visibility"

instance Binary Prog where
  put (Prog mid im tys fus ops) =
    put mid >> put im >> put tys >> put fus >> put ops
  get = Prog <$> get <*> get <*> get <*> get <*> get

instance Binary TypeDecl where
  put (Type    qid vis vs cs) =
    putWord8 0 >> put qid >> put vis >> put vs >> put cs
  put (TypeSyn qid vis vs ty) =
    putWord8 1 >> put qid >> put vis >> put vs >> put ty
  put (TypeNew qid vis vs c ) =
    putWord8 2 >> put qid >> put vis >> put vs >> put c

  get = do
    x <- getWord8
    case x of
      0 -> liftM4 Type get get get get
      1 -> liftM4 TypeSyn get get get get
      2 -> liftM4 TypeNew get get get get
      _ -> fail "Invalid encoding for TypeDecl"

instance Binary ConsDecl where
  put (Cons qid arity vis tys) = put qid >> put arity >> put vis >> put tys
  get = Cons <$> get <*> get <*> get <*> get

instance Binary NewConsDecl where
  put (NewCons qid vis ty) = put qid >> put vis >> put ty
  get = NewCons <$> get <*> get <*> get

instance Binary TypeExpr where
  put (TVar tv) =
    putWord8 0 >> put tv
  put (FuncType ty1 ty2) =
    putWord8 1 >> put ty1 >> put ty2
  put (TCons qid tys) =
    putWord8 2 >> put qid >> put tys
  put (ForallType vs ty) =
    putWord8 3 >> put vs >> put ty

  get = do
    x <- getWord8
    case x of
      0 -> fmap TVar get
      1 -> liftM2 FuncType get get
      2 -> liftM2 TCons get get
      3 -> liftM2 ForallType get get
      _ -> fail "Invalid encoding for TypeExpr"

instance Binary Kind where
  put KStar          = putWord8 0
  put (KArrow k1 k2) = putWord8 1 >> put k1 >> put k2
  get = do
    x <- getWord8
    case x of
      0 -> return KStar
      1 -> liftM2 KArrow get get
      _ -> fail "Invalid encoding for Kind"

instance Binary OpDecl where
  put (Op qid fix pr) = put qid >> put fix >> put pr
  get = liftM3 Op get get get

instance Binary Fixity where
  put InfixOp  = putWord8 0
  put InfixlOp = putWord8 1
  put InfixrOp = putWord8 2

  get = do
    x <- getWord8
    case x of
      0 -> return InfixOp
      1 -> return InfixlOp
      2 -> return InfixrOp
      _ -> fail "Invalid encoding for Fixity"

instance Binary FuncDecl where
  put (Func qid arity vis ty r) =
    put qid >> put arity >> put vis >> put ty >> put r
  get = Func <$> get <*> get <*> get <*> get <*> get

instance Binary Rule where
  put (Rule     alts e) = putWord8 0 >> put alts >> put e
  put (External n     ) = putWord8 1 >> put n

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 Rule get get
      1 -> fmap External get
      _ -> fail "Invalid encoding for TRule"

instance Binary Expr where
  put (Var v) = putWord8 0 >> put v
  put (Lit l) = putWord8 1 >> put l
  put (Comb cty qid es) =
    putWord8 2 >> put cty >> put qid >> put es
  put (Let  bs e) = putWord8 3 >> put bs >> put e
  put (Free vs e) = putWord8 4 >> put vs >> put e
  put (Or  e1 e2) = putWord8 5 >> put e1 >> put e2
  put (Case cty ty as) = putWord8 6 >> put cty >> put ty >> put as
  put (Typed e ty) = putWord8 7 >> put e >> put ty

  get = do
    x <- getWord8
    case x of
      0 -> fmap Var get
      1 -> fmap Lit get
      2 -> liftM3 Comb get get get
      3 -> liftM2 Let get get
      4 -> liftM2 Free get get
      5 -> liftM2 Or get get
      6 -> liftM3 Case get get get
      7 -> liftM2 Typed get get
      _ -> fail "Invalid encoding for TExpr"

instance Binary BranchExpr where
  put (Branch p e) = put p >> put e
  get = liftM2 Branch get get

instance Binary Pattern where
  put (Pattern  qid vs) = putWord8 0 >> put qid >> put vs
  put (LPattern l     ) = putWord8 1 >> put l

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 Pattern get get
      1 -> fmap LPattern get
      _ -> fail "Invalid encoding for TPattern"

instance Binary Literal where
  put (Intc   i) = putWord8 0 >> put i
  put (Floatc f) = putWord8 1 >> put f
  put (Charc  c) = putWord8 2 >> put c

  get = do
    x <- getWord8
    case x of
      0 -> fmap Intc get
      1 -> fmap Floatc get
      2 -> fmap Charc get
      _ -> fail "Invalid encoding for Literal"

instance Binary CombType where
  put FuncCall = putWord8 0
  put ConsCall = putWord8 1
  put (FuncPartCall i) = putWord8 2 >> put i
  put (ConsPartCall i) = putWord8 3 >> put i

  get = do
    x <- getWord8
    case x of
      0 -> return FuncCall
      1 -> return ConsCall
      2 -> fmap FuncPartCall get
      3 -> fmap ConsPartCall get
      _ -> fail "Invalid encoding for CombType"

instance Binary CaseType where
  put Rigid = putWord8 0
  put Flex  = putWord8 1

  get = do
    x <- getWord8
    case x of
      0 -> return Rigid
      1 -> return Flex
      _ -> fail "Invalid encoding for CaseType"
