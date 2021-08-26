module Defaulting where

default (Int, Complex)

class C a where
  methodC :: a -> Bool

instance C [a] where
  methodC _ = True

data Complex = Complex Float Float
  deriving Show

instance Num Complex where
  Complex a b + Complex c d = Complex (a + c) (b + d)
  Complex a b - Complex c d = Complex (a - c) (b - d)
  Complex a b * Complex c d = Complex (a * c - b * d) (a * d + b * c)
  abs (Complex a b) = Complex (sqrt (a * a + b * b)) 0.0
  signum z@(Complex a b) | a == 0.0 && b == 0.0 = Complex 0.0 0.0
                         | otherwise            = z / abs z
  fromInt a = Complex (fromInt a) 0.0

instance Fractional Complex where
  Complex a b / Complex c d = Complex ((a * c + b * d) / (c * c + d * d))
                                      ((b * c - a * d) / (c * c + d * d))
  fromFloat a = Complex a 0.0

-- Expected result: "1"
testExp1 :: String
testExp1 = show 1

-- Expected result: ("1", True)
testExp2 :: (String, Bool)
testExp2 = let x = 1 in (show x, methodC [x])

-- Expected result: "Complex 1.0 0.0"
testExp3 :: String
testExp3 = show (1 / 1)
