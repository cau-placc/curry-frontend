{- |
    Module      :  $Header$
    Description :  A quick fix for a diagnostic
    License     :  BSD-3-clause

    Stability   :  experimental
    Portability :  portable

    This module implements a type for representing fixes for diagnostics.
-}
module Curry.Base.QuickFix
  ( QuickFix (..), insertFix, prependFix, replaceFix
  , insertLineBelowFix, insertAlignedLineBelowFix
  ) where

import Curry.Base.Position (Position (..), nl, HasPosition (..))
import Curry.Base.SpanInfo (HasSpanInfo (..), getStartPosition, getSrcSpan, getSrcSpanEnd)
import Curry.Base.TextEdit (TextEdit (..), insertEdit, replaceEdit)

data QuickFix = QuickFix
  { fixEdit        :: TextEdit
  , fixDescription :: String
  }
  deriving (Eq, Ord, Show)

-- |Creates a fix inserting the given text at the given position.
insertFix :: HasPosition p => p -> String -> String -> QuickFix
insertFix s txt = QuickFix (insertEdit p txt)
  where p = getPosition s

-- |Creates a fix prepending to the given entity the given text and using the given description.
prependFix :: HasSpanInfo s => s -> String -> String -> QuickFix
prependFix s txt = QuickFix (insertEdit p txt)
  where p = getStartPosition s

-- |Creates a fix replacing the given entity with the given text and the given description.
replaceFix :: HasSpanInfo s => s -> String -> String -> QuickFix
replaceFix s txt = QuickFix (replaceEdit sp txt)
  where sp = getSrcSpan s

-- |Creates a fix inserting a line below the given entity with the given description.
insertLineBelowFix :: HasSpanInfo s => s -> String -> String -> QuickFix
insertLineBelowFix s txt = QuickFix (insertEdit p' (txt ++ "\n"))
  where p  = getSrcSpanEnd s
        p' = nl p

-- |Creates a fix inserting an indented line exactly below the given entity with the given description.
insertAlignedLineBelowFix :: HasSpanInfo s => s -> String -> String -> QuickFix
insertAlignedLineBelowFix s txt = QuickFix (insertEdit p' (replicate n ' ' ++ txt ++ "\n"))
  where p1 = getStartPosition s
        p2 = getSrcSpanEnd s
        p' = nl p2
        n  = column p1 - 1
