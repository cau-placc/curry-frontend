{-# LANGUAGE RankNTypes #-}

constFun :: a -> (forall b. b -> b) -> a
constFun = error "fail"

idConstFunTest = id constFun

constFunTest :: a -> (forall b. b -> b) -> a
constFunTest x f = constFun x $ f

applyMaybe :: Maybe a -> (forall b. b -> b) -> a
applyMaybe Nothing  _ = error "fail"
applyMaybe (Just x) f = f x

applyMaybe' :: (forall b. b -> b) -> Maybe a -> a
applyMaybe' = flip applyMaybe
