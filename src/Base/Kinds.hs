{- |
    Module      :  $Header$
    Description :  Internal representation of kinds
    Copyright   :  (c) 2016-2022 Finn Teegen
                       2023      Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module modules provides the definitions for the internal
   representation of kinds in the compiler.

   The functions 'tokind' and 'fromKind' convert Curry kind expressions into
   kinds and vice versa.

   When Curry kinds are converted with 'fromKind', kind variables are
   instantiated with the kind *.
-}

module Base.Kinds where

import Curry.Base.Pretty (Pretty(..))
import Curry.Syntax.Type (KindExpr (..))
import Curry.Syntax.Pretty ()

-- A kind is either *, which is the kind of a value's type, a kind
-- variable, or an arrow kind. Kind variables are used internally during
-- kind inference. Kind variables are not supported in Curry kind
-- expressions and all kind variables that remain free after kind
-- inference are instantiated to *.

data Kind = KindStar
          | KindVariable Int
          | KindArrow Kind Kind
  deriving (Eq, Show)

-- |The function 'kindArity' computes the arity n of a kind.
kindArity :: Kind -> Int
kindArity (KindArrow _ k) = 1 + kindArity k
kindArity _               = 0

-- |The function 'kindVars' returns a list of all kind variables
-- occurring in a kind.
kindVars :: Kind -> [Int]
kindVars k = vars k []
  where
    vars KindStar          kvs = kvs
    vars (KindVariable kv) kvs = kv : kvs
    vars (KindArrow k1 k2) kvs = vars k1 $ vars k2 kvs

-- |The function 'defaultKind' instantiates all kind variables
-- occurring in a kind to *.
defaultKind :: Kind -> Kind
defaultKind (KindArrow k1 k2) = KindArrow (defaultKind k1) (defaultKind k2)
defaultKind _                 = KindStar

-- |The function 'simpleKind' returns the kind of a type
-- constructor with arity n whose arguments all have kind *.
simpleKind :: Int -> Kind
simpleKind n = foldr KindArrow KindStar $ replicate n KindStar

-- |The function 'isSimpleKind' returns whether a kind is simple or not.
isSimpleKind :: Kind -> Bool
isSimpleKind k = k == simpleKind (kindArity k)

-- |Fetches a kind's 'arguments', i.e. everything before an
-- arrow at the top-level. For example: A kind k1 -> k2 -> k3
-- would have the arguments [k1, k2].
kindArgs :: Kind -> [Kind]
kindArgs (KindArrow k k') = k : kindArgs k'
kindArgs _                = []

toKind :: KindExpr -> Kind
toKind Star              = KindStar
toKind (ArrowKind k1 k2) = KindArrow (toKind k1) (toKind k2)

toKind' :: Maybe KindExpr -> Int -> Kind
toKind' k n = maybe (simpleKind n) toKind k

fromKind :: Kind -> KindExpr
fromKind KindStar          = Star
fromKind (KindVariable  _) = Star
fromKind (KindArrow k1 k2) = ArrowKind (fromKind k1) (fromKind k2)

fromKind' :: Kind -> Int -> Maybe KindExpr
fromKind' k n | k == simpleKind n = Nothing
              | otherwise         = Just (fromKind k)

instance Pretty Kind where
  pPrint = pPrintPrec 0 . fromKind
