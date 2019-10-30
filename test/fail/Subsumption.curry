{-# LANGUAGE RankNTypes #-}

applyFun :: (forall a. a -> a) -> b -> b
applyFun f x = f x

idFun :: (a -> a) -> (a -> a)
idFun f = f

applyFunTest :: Bool
applyFunTest = applyFun idFun True

idBool :: Bool -> Bool
idBool = id

applyFunBoolTest :: Bool
applyFunBoolTest = applyFun idBool True

applyEqFun :: Eq a => (forall a. Eq a => a -> a -> Bool) -> a -> a -> Bool
applyEqFun f x y = x `f` y

applyEqFunTest :: Bool
applyEqFunTest = applyEqFun ((==) :: Bool -> Bool -> Bool) True False

trueFun :: (forall a. Eq a => a) -> Bool
trueFun _ = True

trueFunTest :: Bool
trueFunTest = trueFun False

fun1 :: ((forall a b. Eq a => a -> b) -> Bool) -> Bool
fun1 _ = True

fun2 :: (forall a b. a -> b) -> Bool
fun2 _ = True

subsumTest1 :: Bool
subsumTest1 = fun1 fun2
