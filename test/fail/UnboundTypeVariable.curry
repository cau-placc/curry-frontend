{-# LANGUAGE RankNTypes #-}

applyFst :: forall b. (forall a. a -> a) -> b -> a -> b
applyFst f x _ = f x

data A a = A { funA :: a -> b }

type B b = (c, b)
