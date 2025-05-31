{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

class Mult a b c | a b -> c where
  mult :: a -> b -> c

instance Mult a b c => Mult a [b] [c] where
  mult a = map (mult a)
