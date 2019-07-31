{-# LANGUAGE RankNTypes #-}

constFun :: a -> (forall b. b -> b) -> a
constFun = error "fail"

constFunTest :: a -> (forall b. b -> b) -> a
constFunTest x f = constFun x $ f
