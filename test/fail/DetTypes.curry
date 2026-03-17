
{-# LANGUAGE DeterminismSignatures #-}

coin :? Any
coin :: Bool
coin = True
coin = False

coinWrong :? Det
coinWrong :: Bool
coinWrong = True
coinWrong = False

coinProxyWrong :? Det
coinProxyWrong :: Bool
coinProxyWrong = coin

const :? b -> a -> a
const :: b -> a -> a
const _ a' = a'

test2 :? Det
test2 :: Bool
test2 = const coin coin

(<>) :? Det -> Det -> a -> Det
(<>) :: (b -> c) -> (a -> b) -> a -> c
(<>) f g x = f (g x)

not :: Bool -> Bool
not :? a -> a
not True = False
not False = True

class A a where
  a :: (a, Bool)
  a :? Det
  a = (b', True)
    where (b', _) = a

instance A Bool where
  a = (True, coin)

class B b where
  (===) :: b -> b -> Bool
  (===) :? Det -> Det -> Det
  (===) = (===)

  aValue :? Any
  aValue :: b
  aValue = aValue

instance B Bool where
   (===) = (==)

class Eq a where
  (==) :: a -> a -> Bool
  (==) = (==)

instance Eq Bool where
  True == True = True
  False == False = True
  True == False = False
  False == True = False

data Container a = Container a

g2 :? Det -> Any
g2 :: Bool -> Bool
g2 x = id x
g2 x = not x

containerFunc1 :? Det
containerFunc1 :: Container (Bool -> Bool)
containerFunc1 = Container g2

containerFunc1' :? Det -> Det
containerFunc1' :: Bool -> Bool
containerFunc1' = case Container g2 of
  Container f ->  f
