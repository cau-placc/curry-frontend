module NoRedundant where

import Prelude hiding (Eq)

class Eq a where
  eq :: a -> a -> Bool

f :: (Eq a, Ord a) => a -> Bool
f a | a >  a    = True
    | a == a    = False
    | otherwise = True
