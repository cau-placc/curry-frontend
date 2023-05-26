module MultipleInstances where

instance Eq (a -> b) where
  _ == _ = True

instance Eq (a -> b) where
  _ == _ = False
