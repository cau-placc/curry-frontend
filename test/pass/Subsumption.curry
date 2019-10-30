{-# LANGUAGE RankNTypes #-}

fun :: ((forall a b. a -> b) -> Bool) -> Bool
fun _ = True

funPred :: ((forall a b. Eq a => a -> b) -> Bool) -> Bool
funPred _ = True

fun1 :: (forall a b. [Maybe a] -> [Maybe b]) -> Bool
fun1 _ = True

fun2 :: (forall a. [Maybe a] -> [Maybe a]) -> Bool
fun2 _ = True

fun3 :: (forall a. Eq a => a -> a) -> Bool
fun3 _ = True

fun4 :: (forall a b. Eq a => a -> b) -> Bool
fun4 _ = True

fun5 :: (forall a b. Ord a => a -> b) -> Bool
fun5 _ = True

fun6 :: (forall a b. (Eq a, Ord b) => a -> b) -> Bool
fun6 _ = True

fun7 :: (forall a. Eq a => a -> Int) -> Bool
fun7 _ = True

fun8 :: (a -> b) -> Bool
fun8 _ = True

subsumTest1 :: Bool
subsumTest1 = fun fun1

subsumTest2 :: Bool
subsumTest2 = fun fun2

subsumTest3 :: Bool
subsumTest3 = fun fun3

subsumTest4 :: Bool
subsumTest4 = fun fun4

subsumTest5 :: Bool
subsumTest5 = funPred fun5

subsumTest6 :: Bool
subsumTest6 = funPred fun6

subsumTest7 :: Bool
subsumTest7 = funPred fun7

subsumTest8 :: Bool
subsumTest8 = fun fun8
