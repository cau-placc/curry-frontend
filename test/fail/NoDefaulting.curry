{-# LANGUAGE MultiParamTypeClasses #-}

module NoDefaulting where

class C a where
  methodC :: a -> a

instance C Int where
  methodC x = -x

class D a b where
  methodD :: a -> b -> Bool

instance D [a] [a] where
  methodD _ _ = True

testExp1 = show (methodC 5)

testExp2 = let x   = 1
               str = show x
           in (length [methodC x], str)

testExp3 = methodD [1] [2] 

class E

instance E => Fractional Int where
  fromFloat = round

testFunc x = case x of 1.0 -> show (succ x)
                       _   -> show (succ 1.0)
