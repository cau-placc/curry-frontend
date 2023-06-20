{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

class Test a b | a -> b where
  test :: a -> b

instance Test Int Bool where
   test = even

use :: (Test a b, Test b a) => a -> a
use = test . test

useSpec :: Int -> Int
useSpec = use

