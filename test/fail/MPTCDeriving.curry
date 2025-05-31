{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCDeriving where

class C a b

instance C a a => C [a] [a]

data Foo a b = Foo a b

instance C a b => Eq (Foo a b)

data T1 a = T1 (Foo [a] [a])
  deriving Eq

data T2 a b = T2 (Foo [a] [b])
  deriving Eq

instance C (a, b) (b, c)

instance C (a, b) (c, b)

instance C a b => Show (Foo a b)

data T3 a b = T3 (Foo (a, b) (b, b))
  deriving Show
