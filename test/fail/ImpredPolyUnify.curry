{-# LANGUAGE RankNTypes #-}

constFun :: a -> (forall b. b -> b) -> a
constFun = error "fail"
