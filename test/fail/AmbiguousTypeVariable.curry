{-# LANGUAGE RankNTypes #-}

class A b where
  funA :: forall a. a -> b -> a

instance A Bool where
  funA = const

applyFun :: (forall b. b -> b -> b) -> a -> a -> a
applyFun f x y = f x y

applyFunTest :: Bool
applyFunTest = applyFun funA True False

applyFunTest2 :: Char
applyFunTest2 = applyFun funA 'a' 'b'
