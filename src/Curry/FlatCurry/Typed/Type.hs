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

module Curry.FlatCurry.Typed.Type
  ( module Curry.FlatCurry.Typed.Type
  , module Curry.FlatCurry.Typeable
  , module Curry.FlatCurry.Type
  ) where

import Data.Binary
import Control.Monad

import Curry.FlatCurry.Typeable
import Curry.FlatCurry.Type ( QName, VarIndex, Visibility (..), TVarIndex
                            , TypeDecl (..), Kind (..), OpDecl (..), Fixity (..)
                            , TypeExpr (..), ConsDecl (..), NewConsDecl (..)
                            , Literal (..), CombType (..), CaseType (..)
                            )

data TProg = TProg String [String] [TypeDecl] [TFuncDecl] [OpDecl]
  deriving (Eq, Read, Show)

data TFuncDecl = TFunc QName Int Visibility TypeExpr TRule
  deriving (Eq, Read, Show)

data TRule
  = TRule     [(VarIndex, TypeExpr)] TExpr
  | TExternal TypeExpr String
  deriving (Eq, Read, Show)

data TExpr
  = TVarE  TypeExpr VarIndex -- otherwise name clash with TypeExpr's TVar
  | TLit   TypeExpr Literal
  | TComb  TypeExpr CombType QName [TExpr]
  | TLet   [((VarIndex, TypeExpr), TExpr)] TExpr
  | TFree  [(VarIndex, TypeExpr)] TExpr
  | TOr    TExpr TExpr
  | TCase  CaseType TExpr [TBranchExpr]
  | TTyped TExpr TypeExpr
  deriving (Eq, Read, Show)

data TBranchExpr = TBranch TPattern TExpr
  deriving (Eq, Read, Show)

data TPattern
  = TPattern  TypeExpr QName [(VarIndex, TypeExpr)]
  | TLPattern TypeExpr Literal
  deriving (Eq, Read, Show)

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

instance Binary TProg where
  put (TProg mid im tys fus ops) =
    put mid >> put im >> put tys >> put fus >> put ops
  get = TProg <$> get <*> get <*> get <*> get <*> get

instance Binary TFuncDecl where
  put (TFunc qid arity vis ty r) =
    put qid >> put arity >> put vis >> put ty >> put r
  get = TFunc <$> get <*> get <*> get <*> get <*> get

instance Binary TRule where
  put (TRule     alts e) = putWord8 0 >> put alts >> put e
  put (TExternal ty n  ) = putWord8 1 >> put ty   >> put n

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 TRule get get
      1 -> liftM2 TExternal get get
      _ -> fail "Invalid encoding for TRule"

instance Binary TExpr where
  put (TVarE ty v) = putWord8 0 >> put ty >> put v
  put (TLit  ty l) = putWord8 1 >> put ty >> put l
  put (TComb ty cty qid es) =
    putWord8 2 >> put ty >> put cty >> put qid >> put es
  put (TLet  bs e) = putWord8 3 >> put bs >> put e
  put (TFree vs e) = putWord8 4 >> put vs >> put e
  put (TOr  e1 e2) = putWord8 5 >> put e1 >> put e2
  put (TCase cty ty as) = putWord8 6 >> put cty >> put ty >> put as
  put (TTyped e ty) = putWord8 7 >> put e >> put ty

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 TVarE get get
      1 -> liftM2 TLit get get
      2 -> liftM4 TComb get get get get
      3 -> liftM2 TLet get get
      4 -> liftM2 TFree get get
      5 -> liftM2 TOr get get
      6 -> liftM3 TCase get get get
      7 -> liftM2 TTyped get get
      _ -> fail "Invalid encoding for TExpr"

instance Binary TBranchExpr where
  put (TBranch p e) = put p >> put e
  get = liftM2 TBranch get get

instance Binary TPattern where
  put (TPattern  ty qid vs) = putWord8 0 >> put ty >> put qid >> put vs
  put (TLPattern ty l     ) = putWord8 1 >> put ty >> put l

  get = do
    x <- getWord8
    case x of
      0 -> liftM3 TPattern get get get
      1 -> liftM2 TLPattern get get
      _ -> fail "Invalid encoding for TPattern"
