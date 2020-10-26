{- |
    Module      : $Header$
    Description : Typeclass of Typeable entities
    Copyright   : (c) 2018        Kai-Oliver Prott
    License     : BSD-3-clause

    Maintainer  : fte@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This module defines a Typeclass for easy access to the type of entites
-}

module Curry.FlatCurry.Typeable (Typeable(..)) where

import Curry.FlatCurry.Type (TypeExpr)

class Typeable a where
  typeOf :: a -> TypeExpr

instance Typeable TypeExpr where
  typeOf = id
