{- |
    Module      :  $Header$
    Description :  TODO
    Copyright   :  (c) 2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   TODO
-}

module Base.PrettyKinds where

import Curry.Base.Pretty

import Base.CurryKinds
import Base.Kinds

instance Pretty Kind where
  pPrint = ppKind
