{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCDefaultMethodImpls where

class C a b where
  methodC1, methodC2 :: a -> b -> Bool
  methodC1 x = not . methodC2 x
  methodC2 x = not . methodC1 x

  methodC3 :: (a, b)

  methodC4 :: Either a b
  methodC4 = let (x, y) = methodC3
             in if methodC2 x y then Left x else Right y

instance C Bool Int where
  methodC1 b i = b || i > 0
  methodC3 = (True, -2)

instance C Bool Bool where
  methodC2 b1 b2 = not (b1 || b2)
  methodC3 = (False, True)
  methodC4 = Right False

-- Expected result: True
testExp1 :: Bool
testExp1 = methodC2 False 0

-- Expected result: Right (-2)
testExp2 :: Either Bool Int
testExp2 = methodC4

-- Expected result: True
testExp3 :: Bool
testExp3 = uncurry methodC1 (methodC3 :: (Bool, Bool))

-- Expected result: Right False
testExp4 :: Either Bool Bool
testExp4 = methodC4
