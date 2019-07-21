{-# LANGUAGE RankNTypes #-}

data Triple a = Triple (Bool, forall b. a -> b, Int)

type List = [forall a. a -> a]

maybeFun :: Maybe (forall a. a -> a) -> Bool
maybeFun Nothing  = False
maybeFun (Just f) = f True

headFun :: [forall a. a -> a] -> (forall b. b -> b)
headFun = head

type Func a = forall b. a -> b -> a

type FuncPair a b = (Func a, Func b)

fstFunc :: (Func Bool, Func Int) -> Func Bool
fstFunc = fst

maybeFunc :: Maybe (Func Bool) -> Func Bool
maybeFunc (Just f) = f
