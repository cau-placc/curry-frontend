{-# LANGUAGE RankNTypes #-}

type Test a = (forall a. a -> a) -> a

data FuncList a = EmptyFuncList a | FuncList (forall a. a -> a) (FuncList a)

idFun :: forall a. Ord a => (forall a. Eq a => a) -> a
idFun x = id x

applyFun :: (forall a. a -> a) -> a -> a
applyFun f x = f x

class A a where
  funA :: a -> (forall a. a -> a)
