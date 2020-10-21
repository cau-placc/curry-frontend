{- |
    Module      :  $Header$
    Description :  Internal representation of kinds
    Copyright   :  (c) 2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module modules provides the definitions for the internal
   representation of kinds in the compiler.
-}

module Base.Kinds where

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
