{- |
    Module      :  $Header$
    Description :  Auxiliary functions
    Copyright   :  (c) 2001 - 2003 Wolfgang Lux
                       2011 - 2015 Björn Peemöler
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The module Utils provides a few simple functions that are
   commonly used in the compiler, but not implemented in the Haskell
   Prelude or standard library.
-}

module Base.Utils
  ( fst3, snd3, thd3, curry3, uncurry3
  , (++!), foldr2, mapAccumM, findDouble, findMultiples, setAt
  ) where

import Control.Monad (MonadPlus, mzero, mplus)

import Data.List     (partition)

infixr 5 ++!

-- The Prelude does not contain standard functions for triples.
-- We provide projection, (un-)currying, and mapping for triples here.

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, y, _) = y

thd3 :: (a, b, c) -> c
thd3 (_, _, z) = z

curry3 :: ((a, b, c) -> d) -> a -> b -> c -> d
curry3 f x y z = f (x,y,z)

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

-- The function (++!) is variant of the list concatenation operator (++)
-- that ignores the second argument if the first is a non-empty list.
-- When lists are used to encode non-determinism in Haskell,
-- this operator has the same effect as the cut operator in Prolog,
-- hence the ! in the name.

(++!) :: [a] -> [a] -> [a]
xs ++! ys = if null xs then ys else xs

-- Fold operations with two arguments lists can be defined using
-- zip and foldl or foldr, resp. Our definitions are unfolded for
-- efficiency reasons.

-- foldl2 :: (a -> b -> c -> a) -> a -> [b] -> [c] -> a
-- foldl2 _ z []       _        = z
-- foldl2 _ z _        []       = z
-- foldl2 f z (x : xs) (y : ys) = foldl2 f (f z x y) xs ys

foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldr2 _ z []       _        = z
foldr2 _ z _        []       = z
foldr2 f z (x : xs) (y : ys) = f x y (foldr2 f z xs ys)

mapAccumM :: (Monad m, MonadPlus p) => (acc -> x -> m (acc, y)) -> acc -> [x]
          -> m (acc, p y)
mapAccumM _ z [] = return (z, mzero)
mapAccumM f z (x:xs) = do
  (z', y) <- f z x
  (z'', ys) <- mapAccumM f z' xs
  return (z'', return y `mplus` ys)

-- The function 'findDouble' checks whether a list of entities is linear,
-- i.e., if every entity in the list occurs only once. If it is non-linear,
-- the first offending object is returned.

findDouble :: Eq a => [a] -> Maybe a
findDouble []   = Nothing
findDouble (x : xs)
  | x `elem` xs = Just x
  | otherwise   = findDouble xs

findMultiples :: Eq a => [a] -> [[a]]
findMultiples []       = []
findMultiples (x : xs)
  | null same = multiples
  | otherwise = (x : same) : multiples
  where (same, other) = partition (==x) xs
        multiples     = findMultiples other

setAt :: Int -> a -> [a] -> [a]
setAt i x xs | i < 0     = xs
             | otherwise = go i xs
  where
    go 0 (_:ys) = x : ys
    go n (y:ys) = y : go (n-1) ys
    go _ [] = []
