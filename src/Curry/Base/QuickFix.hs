{- |
    Module      :  $Header$
    Description :  A quick fix for a diagnostic
    License     :  BSD-3-clause

    Stability   :  experimental
    Portability :  portable

    This module implements a type for representing fixes for diagnostics.
-}
module Curry.Base.QuickFix
  ( QuickFix (..), prependFix, replaceFix
  ) where

import Curry.Base.SpanInfo (HasSpanInfo (..), SpanInfo (..), getStartPosition)
import Curry.Base.TextEdit (TextEdit (..), insertEdit, replaceEdit)

data QuickFix = QuickFix
  { fixEdit        :: TextEdit
  , fixDescription :: String
  }
  deriving (Eq, Ord, Show)

-- |Creates a fix prepending to the given entity the given text and using the given description.
prependFix :: HasSpanInfo s => s -> String -> String -> QuickFix
prependFix s txt = QuickFix (insertEdit p txt)
  where p = getStartPosition s

-- |Creates a fix replacing the given entity with the given text and the given description.
replaceFix :: HasSpanInfo s => s -> String -> String -> QuickFix
replaceFix s txt = QuickFix (replaceEdit sp txt)
  where sp = srcSpan $ getSpanInfo s
