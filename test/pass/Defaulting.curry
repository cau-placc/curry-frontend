{-# OPTIONS_FRONTEND -Wno-missing-methods -Wno-missing-signatures #-}

module Defaulting where

default (Int, Complex Int, Complex Float)

class C a where
  methodC :: a -> Bool

instance C [a] where
  methodC _ = True

data Complex a = Complex a a
  deriving Show

instance Num a => Num (Complex a) where
  Complex a b + Complex c d = Complex (a + c) (b + d)
  Complex a b - Complex c d = Complex (a - c) (b - d)
  Complex a b * Complex c d = Complex (a * c - b * d) (a * d + b * c)
  fromInt a = Complex (fromInt a) 0

instance Fractional a => Fractional (Complex a) where
  Complex a b / Complex c d = Complex ((a * c + b * d) / (c * c + d * d))
                                      ((b * c - a * d) / (c * c + d * d))
  fromFloat a = Complex (fromFloat a) 0.0

-- Expected result: "1"
testExp1 :: String
testExp1 = show 1

-- Expected result: ("1", True)
testExp2 :: (String, Bool)
testExp2 = let x = 1 in (show x, methodC [x])

-- Expected result: "Complex 1.0 0.0"
testExp3 :: String
testExp3 = show (1 / 1)

-- Expected type: C a => a -> ([Char], Bool)
testFunc x = (show 1, methodC x)
