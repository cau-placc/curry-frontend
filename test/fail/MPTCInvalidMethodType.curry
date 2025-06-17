{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCInvalidMethodType where

class C a b c where
  methodC1 :: a -> c -> a
  methodC2 :: Eq b => a -> b -> c
  methodC3 :: D b c a b => a -> b -> c

class D a b c d
