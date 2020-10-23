{- |
    Module      : $Header$
    Description : Representation of annotated FlatCurry.
    Copyright   : (c) 2016 - 2017 Finn Teegen
    License     : BSD-3-clause

    Maintainer  : fte@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    TODO
-}

module Curry.FlatCurry.Annotated.Type
  ( module Curry.FlatCurry.Annotated.Type
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

data AProg a = AProg String [String] [TypeDecl] [AFuncDecl a] [OpDecl]
  deriving (Eq, Read, Show)

data AFuncDecl a = AFunc QName Int Visibility TypeExpr (ARule a)
  deriving (Eq, Read, Show)

data ARule a
  = ARule     a [(VarIndex, a)] (AExpr a)
  | AExternal a String
  deriving (Eq, Read, Show)

data AExpr a
  = AVar   a VarIndex
  | ALit   a Literal
  | AComb  a CombType (QName, a) [AExpr a]
  | ALet   a [((VarIndex, a), AExpr a)] (AExpr a)
  | AFree  a [(VarIndex, a)] (AExpr a)
  | AOr    a (AExpr a) (AExpr a)
  | ACase  a CaseType (AExpr a) [ABranchExpr a]
  | ATyped a (AExpr a) TypeExpr
  deriving (Eq, Read, Show)

data ABranchExpr a = ABranch (APattern a) (AExpr a)
  deriving (Eq, Read, Show)

data APattern a
  = APattern  a (QName, a) [(VarIndex, a)]
  | ALPattern a Literal
  deriving (Eq, Read, Show)

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

instance Binary a => Binary (AProg a) where
  put (AProg mid im tys fus ops) =
    put mid >> put im >> put tys >> put fus >> put ops
  get = AProg <$> get <*> get <*> get <*> get <*> get

instance Binary a => Binary (AFuncDecl a) where
  put (AFunc qid arity vis ty r) =
    put qid >> put arity >> put vis >> put ty >> put r
  get = AFunc <$> get <*> get <*> get <*> get <*> get

instance Binary a => Binary (ARule a) where
  put (ARule     a alts e) = putWord8 0 >> put a  >> put alts >> put e
  put (AExternal ty n    ) = putWord8 1 >> put ty >> put n

  get = do
    x <- getWord8
    case x of
      0 -> liftM3 ARule get get get
      1 -> liftM2 AExternal get get
      _ -> fail "Invalid encoding for TRule"

instance Binary a => Binary (AExpr a) where
  put (AVar a v) = putWord8 0 >> put a >> put v
  put (ALit a l) = putWord8 1 >> put a >> put l
  put (AComb a cty qid es) =
    putWord8 2 >> put a >> put cty >> put qid >> put es
  put (ALet  a bs e ) = putWord8 3 >> put a >> put bs >> put e
  put (AFree a vs e ) = putWord8 4 >> put a >> put vs >> put e
  put (AOr   a e1 e2) = putWord8 5 >> put a >> put e1 >> put e2
  put (ACase a cty ty as) = putWord8 6 >> put a >> put cty >> put ty >> put as
  put (ATyped a e ty) = putWord8 7 >> put a >> put e >> put ty

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 AVar get get
      1 -> liftM2 ALit get get
      2 -> liftM4 AComb get get get get
      3 -> liftM3 ALet get get get
      4 -> liftM3 AFree get get get
      5 -> liftM3 AOr get get get
      6 -> liftM4 ACase get get get get
      7 -> liftM3 ATyped get get get
      _ -> fail "Invalid encoding for TExpr"

instance Binary a => Binary (ABranchExpr a) where
  put (ABranch p e) = put p >> put e
  get = liftM2 ABranch get get

instance Binary a => Binary (APattern a) where
  put (APattern  a qid vs) = putWord8 0 >> put a >> put qid >> put vs
  put (ALPattern a l     ) = putWord8 1 >> put a >> put l

  get = do
    x <- getWord8
    case x of
      0 -> liftM3 APattern get get get
      1 -> liftM2 ALPattern get get
      _ -> fail "Invalid encoding for TPattern"
