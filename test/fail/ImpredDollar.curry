{-# LANGUAGE RankNTypes #-}

import Prelude hiding (($))

infixr 0 $

($) :: (a -> b) -> a -> b
f $ x = f x

constFun :: a -> (forall b. b -> b) -> a
constFun x _ = x

constFunTest :: a -> (forall b. b -> b) -> a
constFunTest x f = constFun x $ f
