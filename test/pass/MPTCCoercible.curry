{-# LANGUAGE MultiParamTypeClasses, FunctionalPatterns #-}

module MPTCCoercible where

class Coercible a b where
  coerce :: a -> b

instance Coercible Int Int where
  coerce = id

instance Coercible Bool Int where
  coerce False = 0
  coerce True  = 1

instance Coercible Int Bool where
  coerce n | n == 0    = False
           | otherwise = True

instance Coercible a b => Coercible [a] [b] where
  coerce = map coerce

instance (Coercible a c, Coercible b d) => Coercible (a, b) (c, d) where
  coerce (x, y) = (coerce x, coerce y)

uncoerce :: (Coercible b a, Data a, Data b) => a -> b
uncoerce (coerce x) = x

-- Expected result: True
testExp1 :: Bool
testExp1 = coerce (coerce True :: Int)

-- Expected result: [(1, False), (0, True)]
testExp2 :: [(Int, Bool)]
testExp2 = coerce [(True, 0 :: Int), (False, 42)]

-- Expected result: [True, False, False, True]
testExp3 :: [Bool]
testExp3 = uncoerce [1 :: Int, 0, 0, 1]
