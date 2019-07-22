{-# LANGUAGE RankNTypes #-}

applyFst :: forall b. (forall a. a -> a) -> b -> a -> b
applyFst f x _ = f x
