{-# LANGUAGE RankNTypes #-}

idBool :: Bool -> Bool
idBool = id

applyFun :: (forall a. a -> a) -> b -> b
applyFun f x = f x

applyFunBoolTest :: Bool
applyFunBoolTest = applyFun idBool True

idFun :: (a -> a) -> (a -> a)
idFun f = f

applyFunTest :: Bool
applyFunTest = applyFun idFun True

trueFun :: (forall a. Eq a => a) -> Bool
trueFun _ = True

trueFunTest :: Bool
trueFunTest = trueFun False

applyEqFun :: Eq a => (forall a. Eq a => a -> a -> Bool) -> a -> a -> Bool
applyEqFun f x y = x `f` y

applyEqFunTest :: Bool
applyEqFunTest = applyEqFun ((==) :: Bool -> Bool -> Bool) True False
