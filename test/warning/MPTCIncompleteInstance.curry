{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCIncompleteInstance where

class C a b where
  methodC1 :: a -> b
  methodC2 :: a -> b -> Bool
  methodC2 _ _ = False
  methodC3 :: b -> a

class D where
  methodD1 :: Foo
  methodD1 = Foo
  methodD2 :: Bool

class E where
  methodE :: Bool

data Foo = Foo

instance C Bool Foo where
  methodC1 _ = Foo

instance D
