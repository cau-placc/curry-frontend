{- |
    Module      : $Header$
    Description : Representation of annotated FlatCurry.
    Copyright   : (c) 2016 - 2017 Finn Teegen
    License     : BSD-3-clause

    Maintainer  : fte@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This module defines the annotated data structures for FlatCurry programs.
    These structures include annotated versions of programs, function declarations,
    rules, expressions, patterns, and branches. The annotations are used to store
    additional information for each element in the program, making it more flexible
    for further processing.
-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveGeneric  #-}
module Curry.FlatCurry.Annotated.Type
  ( module Curry.FlatCurry.Annotated.Type
  , module Curry.FlatCurry.Typeable
  , module Curry.FlatCurry.Type
  ) where

import Data.Binary  (Binary)
import GHC.Generics (Generic)

import Curry.FlatCurry.Typeable
import Curry.FlatCurry.Type ( QName, VarIndex, Visibility (..), TVarIndex
                            , TypeDecl (..), Kind (..), OpDecl (..), Fixity (..)
                            , TypeExpr (..), ConsDecl (..), NewConsDecl (..)
                            , Literal (..), CombType (..), CaseType (..)
                            )

data AProg a = AProg String [String] [TypeDecl] [AFuncDecl a] [OpDecl]
  deriving (Eq, Read, Show, Generic, Binary)

data AFuncDecl a = AFunc QName Int Visibility TypeExpr (ARule a)
  deriving (Eq, Read, Show, Generic, Binary)

data ARule a
  = ARule     a [(VarIndex, a)] (AExpr a)
  | AExternal a String
  deriving (Eq, Read, Show, Generic, Binary)

data AExpr a
  = AVar   a VarIndex
  | ALit   a Literal
  | AComb  a CombType (QName, a) [AExpr a]
  | ALet   a [((VarIndex, a), AExpr a)] (AExpr a)
  | AFree  a [(VarIndex, a)] (AExpr a)
  | AOr    a (AExpr a) (AExpr a)
  | ACase  a CaseType (AExpr a) [ABranchExpr a]
  | ATyped a (AExpr a) TypeExpr
  deriving (Eq, Read, Show, Generic, Binary, Functor)

data ABranchExpr a = ABranch (APattern a) (AExpr a)
  deriving (Eq, Read, Show, Generic, Binary, Functor)

data APattern a
  = APattern  a (QName, a) [(VarIndex, a)]
  | ALPattern a Literal
  deriving (Eq, Read, Show, Generic, Binary, Functor)

instance Typeable a => Typeable (AExpr a) where
  typeOf (AVar a _) = typeOf a
  typeOf (ALit a _) = typeOf a
  typeOf (AComb a _ _ _) = typeOf a
  typeOf (ALet a _ _) = typeOf a
  typeOf (AFree a _ _) = typeOf a
  typeOf (AOr a _ _) = typeOf a
  typeOf (ACase a _ _ _) = typeOf a
  typeOf (ATyped a _ _) = typeOf a

instance Typeable a => Typeable (APattern a) where
  typeOf (APattern a _ _) = typeOf a
  typeOf (ALPattern a _) = typeOf a
