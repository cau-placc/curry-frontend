{-# LANGUAGE RankNTypes #-}

constFunFail :: a -> (forall b. b -> b) -> a
constFunFail = error "fail"

constFun :: a -> (forall b. b -> b) -> a
constFun x _ = x

idConstFunTest = id constFun

constFunTest :: a -> (forall b. b -> b) -> a
constFunTest x f = ($) (constFun x) f

constFunLeftSectionTest :: a -> (forall b. b -> b) -> a
constFunLeftSectionTest x f = (constFun x $) f

constFunRightSectionTest :: a -> (forall b. b -> b) -> a
constFunRightSectionTest x f = constFun x ($ f)

applyMaybe :: Maybe a -> (forall b. b -> b) -> a
applyMaybe Nothing  _ = error "fail"
applyMaybe (Just x) f = f x

applyMaybe' :: (forall b. b -> b) -> Maybe a -> a
applyMaybe' = flip applyMaybe
