{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCWrongKind where

class C a b where
  methodC :: a b

instance C Bool []

class C b a => D a b where
  methodD :: a Bool -> b

class C a a => E a

class F a b where
  methodF1 :: a b
  methodF2 :: b a
