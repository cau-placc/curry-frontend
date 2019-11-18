{-# LANGUAGE ExplicitForAll #-}

idFun :: forall a. a -> a
idFun = id

constFun :: forall a b. a -> b -> b
constFun = const

unknownTest :: forall a. Data a => a
unknownTest = unknown
