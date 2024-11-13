{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

module MPTCInstanceOverlap where

class C a b c where
  methodC :: a -> b -> c -> Bool

instance C [a] [a] [b] where
  methodC _ _ _ = True

instance C [a] [b] [b] where
  methodC _ _ _ = False

f1 = methodC [True] [True] [True]

f2 :: a -> a -> a -> Bool
f2 x y z = methodC [x] [y] [z]

f3 x y = let b = methodC [x] [y] [y] in b && x == y

f4 x y z = methodC [x] [y] [z]

f5 :: Bool -> Bool
f5 x = let f' :: Bool -> Bool
           f' y = methodC [x] [y] [y]
       in f' True

f6 x = let f' y = methodC [x] [y] [y]
       in f' True && x
