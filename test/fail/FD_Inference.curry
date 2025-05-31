{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

class C a b | a -> b


f :: (C a b, C a c) => a -> b -> c
f _ = id
  




