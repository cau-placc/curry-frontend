module Red where

import qualified Prelude as P

f :: (P.Eq a, P.Ord a) => a -> P.Bool
f a | a P.>  a    = P.True
    | a P.== a    = P.False
    | P.otherwise = P.True
