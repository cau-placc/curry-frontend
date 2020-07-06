module Redundant where

f :: (Eq a, Ord a) => a -> Bool
f a | a >  a    = True
    | a == a    = False
    | otherwise = True
