{-# LANGUAGE RankNTypes #-}

type Test a = (forall a. a -> a) -> a

applyFun :: (forall a. a -> a) -> a -> a
applyFun f x = f x

class A a where
  funA :: a -> (forall a. a -> a)
