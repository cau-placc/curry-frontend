{-# LANGUAGE RankNTypes #-}

newtype ChurchList a =
  ChurchList { runList :: forall r. (a -> r -> r) -> r -> r }

empty :: ChurchList a
empty = ChurchList $ \_ z -> z

constFun :: a -> (forall b. b -> b) -> a
constFun x _ = x

constFunTest :: a -> (a -> forall b. b -> b) -> a
constFunTest x f = constFun x $ f x
