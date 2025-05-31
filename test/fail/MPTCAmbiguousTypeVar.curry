{-# LANGUAGE FunctionalPatterns, MultiParamTypeClasses #-}

module MPTCAmbiguousTypeVar where

class C a b where
  methodC :: a -> b

f1 = methodC . methodC

class D a b c where
  methodD :: a -> b -> c

f2 (methodD x _) = x
