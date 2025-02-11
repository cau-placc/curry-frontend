{- |
    Module      :  $Header$
    Description :  A quick fix for a diagnostic
    License     :  BSD-3-clause

    Stability   :  experimental
    Portability :  portable

    This module implements a type for representing fixes for diagnostics.
-}
module Curry.Base.QuickFix
  ( QuickFix (..)
  ) where

import Curry.Base.TextEdit (TextEdit (..))

data QuickFix = QuickFix
  { fixEdit        :: TextEdit
  , fixDescription :: String
  }
