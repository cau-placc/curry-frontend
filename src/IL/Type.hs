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

module IL.Type
  ( -- * Data types
    Module (..), Decl (..), ConstrDecl (..), NewConstrDecl (..), Type (..)
  , Literal (..), ConstrTerm (..), Expression (..), Eval (..)
  , Alt (..), Binding (..)
  ) where

import Curry.Base.Ident

import Base.Expr

data Module = Module ModuleIdent [ModuleIdent] [Decl]
    deriving (Eq, Show)

data Decl
  = DataDecl         QualIdent Int [ConstrDecl]
  | NewtypeDecl      QualIdent Int NewConstrDecl
  | ExternalDataDecl QualIdent Int
  | FunctionDecl     QualIdent [(Type, Ident)] Type Expression
  | ExternalDecl     QualIdent Type
    deriving (Eq, Show)

data NewConstrDecl = NewConstrDecl QualIdent Type
    deriving (Eq, Show)

data ConstrDecl = ConstrDecl QualIdent [Type]
    deriving (Eq, Show)

data Type
  = TypeConstructor QualIdent [Type]
  | TypeVariable    Int
  | TypeArrow       Type Type
  | TypeForall      [Int] Type
    deriving (Eq, Show)

data Literal
  = Char  Char
  | Int   Integer
  | Float Double
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
