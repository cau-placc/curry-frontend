{-# LANGUAGE FunctionalPatterns #-}

module MPTCNoExtension where

import MPTCCoercible

class Coercible a a => IdentityCoerce a where
  idCoerce :: a -> a

instance IdentityCoerce Int where
  idCoerce = coerce

instance IdentityCoerce a => IdentityCoerce [a] where
  idCoerce = map idCoerce

doubleIdentityCoerce :: IdentityCoerce a => a -> a
doubleIdentityCoerce = idCoerce . idCoerce

doubleCoerceWithStep :: (Coercible a b, Coercible b c) => a -> (b, c)
doubleCoerceWithStep x = let y = coerce x in (y, coerce y)

-- Expected result: [1, 2, 3, 4]
testExp1 :: [Int]
testExp1 = doubleIdentityCoerce [1, 2, 3, 4]

-- Expected result: ([(1, 0), (0, 42)], [(1, False), (0, True)])
testExp2 :: ([(Int, Int)], [(Int, Bool)])
testExp2 = doubleCoerceWithStep [(True, 0 :: Int), (False, 42)]
