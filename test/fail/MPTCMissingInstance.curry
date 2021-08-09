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

class E a b c where
  methodE :: a -> b -> c -> Bool

instance E [a] [a] [b] where
  methodE _ _ _ = True

instance E [a] [b] [b] where
  methodE _ _ _ = False

f3 x = let f' :: a -> Bool
           f' y = methodE [x] [True] [y]
       in f' True : x
