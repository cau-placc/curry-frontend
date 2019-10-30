{-# LANGUAGE RankNTypes #-}

whereTest :: (forall a. a -> a) -> (Char, Bool)
whereTest = whereTest'
  where
    whereTest' f = (f 'c', f True)
