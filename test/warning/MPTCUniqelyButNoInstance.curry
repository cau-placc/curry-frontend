-- Test for multi-parameter type classes with functional dependencies
-- where a uniquely determined instance is missing
-- and added as a constraint to the test function
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts #-}
module MPTCUniqelyButNoInstance where

-- Unique coerce between two types:
class Coerce a b | a -> b where
  coerce :: a -> b

-- test :: Coerce Char a => a
test = coerce 'a'
