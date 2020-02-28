{-# LANGUAGE RankNTypes #-}

module RankNTypes where

type IdFunc = forall a. a -> a

id' :: IdFunc
id' x = x

fun :: (forall a. a -> a) -> (Char, Bool)
fun f = (f 'c', f True)

fun' :: (forall a . Eq a => a -> a) -> Bool
fun' f = f False

idFun :: (forall a. Eq a => a) -> forall a. Ord a => a
idFun x = x

idFun' :: forall a. Ord a => (forall b. Eq b => b) -> a
idFun' x = id x

idFun'' :: (forall b. Eq b => b) -> forall c. Ord c => c
idFun'' = idFun

idFun'''' :: (forall b . b) a -> (forall b . b) a
idFun'''' x = x

shadow :: forall a m . ((forall a . a m) -> a -> Int)
shadow _ _= 1

idBool :: Bool -> Bool
idBool = id

idFunBoolTest :: Bool
idFunBoolTest = idFunc idBool True
  where
    idFunc :: forall a. (a -> a) -> a -> a
    idFunc f x = f x

applyFun :: forall a b. (a -> b) -> a -> b
applyFun f x = f x

newtype ParserT m a = ParserT { runP :: forall r . (() -> r) -> m a }

runParserT :: forall m a. ParserT m a -> (forall r . () -> r) -> m a
runParserT = runP

data TestT = TestT { runTest :: forall a. forall b. a -> b -> a }

testT :: TestT -> Bool
testT (TestT {runTest = f}) = f True 42

testT' :: TestT -> Bool
testT' t = case t of
  TestT f -> f True 42

lambdaFun :: (forall a. Eq a => a -> a) -> (Int, Bool)
lambdaFun = (\f -> (f 73, f True)) :: (forall b. Ord b => b -> b) -> (Int, Bool)

lambdaFun' :: (Int, Bool)
lambdaFun' = ((\f -> (f 73, f True)) :: (forall b. b -> b) -> (Int, Bool)) id

lambdaFun'' :: Bool -> (Int, Bool)
lambdaFun'' b = case b of
                  True  -> f id
                  False -> g (flip const "fail")
  where
    f :: (forall b. b -> b) -> (Int, Bool)
    f = \h -> (h 73, h True)
    g :: (forall b. b -> b) -> (Int, Bool)
    g h = (h 73, h True)

data FuncList a = EmptyFuncList a | FuncList (forall b. b -> b) (FuncList a)

type FuncListPair a = (FuncList a, FuncList a)

class A b where
  funA :: b -> forall a. a -> a
  funB :: forall a. a -> b -> a

andF :: (forall a. a -> a -> a) -> (forall a. a -> a -> a)
     -> forall a. a -> a -> a
andF = \x y -> x y x

andF' :: (forall a. a -> a -> a) -> (forall a. a -> a -> a)
      -> forall a. a -> a -> a
andF' x y = x y x

orF :: (forall a. a -> a -> a) -> (forall a. a -> a -> a)
    -> forall a. a -> a -> a
orF = \x y -> x x y

orF' :: (forall a. a -> a -> a) -> (forall a. a -> a -> a)
     -> forall a. a -> a -> a
orF' x y = x x y

trueFun :: (forall a. Eq a => a) -> Bool
trueFun _ = True

applyTuple :: forall b c d. (forall a. a -> b) -> (c, d) -> (b, b)
applyTuple f (x, y) = (f x, f y)

data Foo = Foo Bool | Bar String

applyFoo :: Foo -> (forall a. a -> a) -> Foo
applyFoo (Foo x) f = Foo $ f x
applyFoo (Bar x) f = f $ Bar x

applyEqFun :: Eq a => (forall b. Eq b => b -> b -> Bool) -> a -> a -> Bool
applyEqFun f x y = x `f` y

-- applyEqFunTest1 :: Bool
-- applyEqFunTest1 = applyEqFun (==) True False

-- applyEqFunTest2 :: Bool -> Bool -> Bool
-- applyEqFunTest2 = applyEqFun (==)

applyMaybe :: Maybe a -> (forall b. b -> b) -> a
applyMaybe Nothing  _ = error "fail"
applyMaybe (Just x) f = f x

applyMaybe' :: (forall b. b -> b) -> Maybe a -> a
applyMaybe' _ Nothing  = error "fail"
applyMaybe' f (Just x) = f x

type EqFunc = forall a. Eq a => a -> a -> Bool

data Bag _ a = Bag a
data Elem _ a = Elem a

instance Functor (Bag s) where
  fmap f (Bag a) = Bag (f a)

instance Applicative (Bag s) where
  pure = returnBag
  mf <*> ma = do
    f <- mf
    a <- ma
    return (f a)

instance Monad (Bag s) where
  return = returnBag
  (>>=) = bindBag

bindBag :: Bag s a -> (a -> Bag s b) -> Bag s b
bindBag b f = case b of
                Bag x -> f x

returnBag :: a -> forall s. Bag s a
returnBag = Bag

runBag :: forall a. (forall s. Bag s a) -> a
runBag b = case b of
             Bag x -> x

newElem :: a -> (forall s. Bag s (Elem s a))
newElem = Bag . Elem

readElem :: forall s. forall a. (Elem s a -> Bag s a)
readElem e = case e of
               Elem x -> Bag x

getValueFromBag :: String
getValueFromBag = runBag (do e <- newElem "Hello, world!"
                             value <- readElem e
                             return value)

failErr :: forall a. a
failErr = error "fail"

constFun :: (forall a. a -> a) -> _ -> forall b. b -> b
constFun f _ = f

constFun' :: (forall a. a -> a) -> _ -> forall b. b -> b
constFun' = const

constFunTest :: Bool
constFunTest = (id `constFun` 73) True

data Showable = Showable (forall b. (forall a. Show a => a -> b) -> b)

showableTest :: Show a => a -> Showable
showableTest g = Showable (\f -> f g)

showableFun1 :: Showable -> String
showableFun1 (Showable f) = let k x = show x in f k

-- showableFun2 :: Showable -> String
-- showableFun2 (Showable f) = f (\x -> show x)

showableFun3 :: Showable -> String
showableFun3 showable = case showable of
  Showable f -> let k x = show x in f k

showableFun4 :: Showable -> String
showableFun4 showable = case showable of
  Showable f -> f show
