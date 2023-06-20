{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

module MPTCFlexibleContext where

class C a b where
  methodC :: a -> b -> Bool

instance C Bool Bool where
  methodC _ _ = True

instance C Bool Int where
  methodC _ _ = True

f1 = methodC True

f2 = let f2a x = methodC True x
     in f2a True

f3 = let (_, f3a) = (False, methodC True)
     in (f3a True, f3a (1 :: Int))

f4 x = let f4a y = methodC x y && x in f4a True 
