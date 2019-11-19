{-# LANGUAGE ExplicitForAll #-}

idFun :: forall a. a -> a
idFun = id

constFun :: forall a b. a -> b -> a
constFun = const

unknownTest :: forall a. Data a => a
unknownTest = unknown
