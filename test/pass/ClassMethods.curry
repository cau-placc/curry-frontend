class A a where
  funA :: Integral b => a -> b

instance A Float where
  funA _ = error "fail"

class B a where
  funB :: (Integral b, Show c) => a -> b -> c -> a

instance B Float where
  funB x _ _ = x
