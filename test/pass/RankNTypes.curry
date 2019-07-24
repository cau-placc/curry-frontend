{-# LANGUAGE RankNTypes #-}

type IdFunc = forall a. a -> a

id' :: IdFunc
id' x = x

fun :: (forall a. a -> a) -> (Char, Bool)
fun f = (f 'c', f True)

fun' :: (forall a . Eq a => a -> a) -> Bool
fun' f = f False

idFun :: (forall a. Eq a => a) -> forall a. Ord a => a
idFun x = x

idFun' :: (forall a. Eq a => a) -> forall a. Ord a => a
idFun' = id

idFun'' :: forall a. Ord a => (forall b. Eq b => b) -> a
idFun'' x = id x

idFun''' :: (forall b. Eq b => b) -> forall c. Ord c => c
idFun''' = idFun

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
