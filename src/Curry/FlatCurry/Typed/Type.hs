{- |
    Module      : $Header$
    Description : Representation of annotated FlatCurry.
    Copyright   : (c) 2016 - 2017 Finn Teegen
                      2018        Kai-Oliver Prott
    License     : BSD-3-clause

    Maintainer  : fte@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This library contains a version of FlatCurry's abstract syntax tree
    modified with type information

    For more information about the abstract syntax tree of `FlatCurry`,
    see the documentation of the respective module.
-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
module Curry.FlatCurry.Typed.Type
  ( module Curry.FlatCurry.Typed.Type
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

data TProg = TProg String [String] [TypeDecl] [TFuncDecl] [OpDecl]
  deriving (Eq, Read, Show, Generic, Binary)

data TFuncDecl = TFunc QName Int Visibility TypeExpr TRule
  deriving (Eq, Read, Show, Generic, Binary)

data TRule
  = TRule     [(VarIndex, TypeExpr)] TExpr
  | TExternal TypeExpr String
  deriving (Eq, Read, Show, Generic, Binary)

data TExpr
  = TVarE  TypeExpr VarIndex -- otherwise name clash with TypeExpr's TVar
  | TLit   TypeExpr Literal
  | TComb  TypeExpr CombType QName [TExpr]
  | TLet   [((VarIndex, TypeExpr), TExpr)] TExpr
  | TFree  [(VarIndex, TypeExpr)] TExpr
  | TOr    TExpr TExpr
  | TCase  CaseType TExpr [TBranchExpr]
  | TTyped TExpr TypeExpr
  deriving (Eq, Read, Show, Generic, Binary)

data TBranchExpr = TBranch TPattern TExpr
  deriving (Eq, Read, Show, Generic, Binary)

data TPattern
  = TPattern  TypeExpr QName [(VarIndex, TypeExpr)]
  | TLPattern TypeExpr Literal
  deriving (Eq, Read, Show, Generic, Binary)

instance Typeable TRule where
  typeOf (TRule args e) = foldr (FuncType . snd) (typeOf e) args
  typeOf (TExternal ty _) = ty

instance Typeable TExpr where
  typeOf (TVarE ty _) = ty
  typeOf (TLit ty _) = ty
  typeOf (TComb  ty _ _ _) = ty
  typeOf (TLet _ e) = typeOf e
  typeOf (TFree _ e) = typeOf e
  typeOf (TOr e _) = typeOf e
  typeOf (TCase _ _ (e:_)) = typeOf e
  typeOf (TTyped _ ty) = ty
  typeOf (TCase _ _ []) = error $ "Curry.FlatCurry.Typed.Type.typeOf: " ++
                                  "empty list in case expression"

instance Typeable TPattern where
  typeOf (TPattern ty _ _) = ty
  typeOf (TLPattern ty _) = ty

instance Typeable TBranchExpr where
  typeOf (TBranch _ e) = typeOf e
