{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

class C a b | a -> b where
  methodC :: a -> b

-- f :: (C a c, C c b) => a -> b
f = methodC . methodC

-- compose :: (a -> b) -> (b -> c) -> (a -> c)
-- compose f g x = g (f x)
