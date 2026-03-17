{-# LANGUAGE DeterminismSignatures #-}
{-# OPTIONS_FRONTEND -Werror #-}

coin :? Any
coin :: Bool
coin = True
coin = False

const :? b -> a -> a
const :: b -> a -> a
const _ a' = a'

test1 :: a -> a
test1 :? a -> a
test1 = const coin (\a' -> a')

test3 :: Bool
test3 :? Any
test3 = test1 coin

test4 :: Bool
test4 :? Det
test4 = const test1 True

(.) :? (b -> c) -> (a -> b) -> a -> c
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f1 f2 x = f1 (f2 x)

allValues :? Any -> Det
allValues :: a -> a
allValues external

id :: Bool -> Bool
id :? a -> a
id x = x

g1 :: Bool -> Bool
g1 :? Any
g1 = id
g1 = not

testg1 :? Det
testg1 :: Bool -> Bool
testg1 = allValues g1

testg1App1 :? Det
testg1App1 :: Bool
testg1App1 = allValues g1 True

testg1App2 :? Det
testg1App2 :: Bool
testg1App2 = testg1 True

g2 :? Det -> Any
g2 :: Bool -> Bool
g2 x = id x
g2 x = not x

biah :: Bool
biah:? Det
biah external

biab :: Bool
biab :? Det
biab = biah

f :? Det -> Any
f :: Bool -> Bool
f x = g (g x)
  where g _ = True

class A a where
  a :: (a, Bool)
  a :? Det
  a = (b', True)
    where (b', _) = a

b :: A a => (a, Bool)
b :? Det
b = a

class B b where
  (===) :: b -> b -> Bool
  (===) :? Det -> Det -> Det
  (===) = (===)

  aValue :? Any
  aValue :: b
  aValue = aValue

instance B Bool where
  True === True = True
  False === False = True
  True === False = False
  False === True = False

  aValue = True
  aValue = False

(/==) :: B b => b -> b -> Bool
(/==) :? Det -> Det -> Det
x /== y = not (x === y)

class Eq a where
  (==) :: a -> a -> Bool
  (==) = (==)

instance Eq Bool where
  True == True = True
  False == False = True
  True == False = False
  False == True = False

fmapOnFunctions1 :? (a -> b) -> (c -> a) -> c -> b
fmapOnFunctions1 :: (a -> b) -> (c -> a) -> c -> b
fmapOnFunctions1 f' g' c = f' (g' c)

fmapOnFunctions2 :? (Det -> Det) -> (Det -> Det) -> Det -> Det
fmapOnFunctions2 :: (a -> b) -> (c -> a) -> c -> b
fmapOnFunctions2 f' g' c = f' (g' c)

fmapOnFunctions3 :? Det -> Det -> Det
fmapOnFunctions3 :: (a -> b) -> (c -> a) -> c -> b
fmapOnFunctions3 f' g' c = f' (g' c)

data Container a = Container a

container1 :? Det -> Det
container1 :: a -> Container a
container1 = Container

container2 :? Det -> Det
container2 :: a -> Container a
container2 x = Container x

containerFunc2 :? Any
containerFunc2 :: Container (Bool -> Bool)
containerFunc2 = Container g2

containerFunc3 :? Det
containerFunc3 :: Container (Bool -> Bool)
containerFunc3 = Container not

testPartial :? Det -> Det
testPartial :: Bool -> Bool
testPartial = not . (=== True)

($) :? (a -> b) -> a -> b
($) :: (a -> b) -> a -> b
g $ x = g x
