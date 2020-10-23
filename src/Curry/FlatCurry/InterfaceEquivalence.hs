{- |
    Module      :  $Header$
    Description :  Check the equality of two FlatCurry interfaces
    Copyright   :  (c) 2006       , Martin Engelke
                       2011 - 2014, Björn Peemöller
                       2014       , Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable
-}

module Curry.FlatCurry.InterfaceEquivalence (eqInterface) where

import Data.List (deleteFirstsBy)

import Curry.FlatCurry.Type

infix 4 =~=, `eqvSet`

-- |Check whether the interfaces of two FlatCurry programs are equivalent.
eqInterface :: Prog -> Prog -> Bool
eqInterface = (=~=)

-- |Type class to express the equivalence of two values
class Equiv a where
  (=~=) :: a -> a -> Bool

instance Equiv a => Equiv [a] where
  []     =~= []     = True
  (x:xs) =~= (y:ys) = x =~= y && xs =~= ys
  _      =~= _      = False

instance Equiv Char where (=~=) = (==)

-- |Equivalence of lists independent of the order.
eqvSet :: Equiv a => [a] -> [a] -> Bool
xs `eqvSet` ys = null (deleteFirstsBy (=~=) xs ys ++ deleteFirstsBy (=~=) ys xs)

instance Equiv Prog where
  Prog m1 is1 ts1 fs1 os1 =~= Prog m2 is2 ts2 fs2 os2
    = m1 == m2 && is1 `eqvSet` is2 && ts1 `eqvSet` ts2
               && fs1 `eqvSet` fs2 && os1 `eqvSet` os2

instance Equiv TypeDecl where (=~=) = (==)

instance Equiv FuncDecl where
  Func qn1 ar1 vis1 ty1 r1 =~= Func qn2 ar2 vis2 ty2 r2
    = qn1 == qn2 && ar1 == ar2 && vis1 == vis2 && ty1 == ty2 && r1 =~= r2

-- TODO: Check why arguments of rules are not checked for equivalence
instance Equiv Rule where
  Rule _ _   =~= Rule _ _   = True
  External _ =~= External _ = True
  _          =~= _          = False

instance Equiv OpDecl where (=~=) = (==)
