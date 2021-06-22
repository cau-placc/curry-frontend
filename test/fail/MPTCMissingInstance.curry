{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCMissingInstance where

class C a b where
  methodC :: a -> b -> Bool

instance C Bool Bool where
  methodC _ _ = True

instance C [a] [b] where
  methodC _ _ = True

instance C [a] Bool where
  methodC _ _ = True

f1 = methodC True [True]

class D where
  methodD :: Bool

f2 = methodD
