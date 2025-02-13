{- |
    Module      :  $Header$
    Description :  Text edits in a source file
    License     :  BSD-3-clause

    Stability   :  experimental
    Portability :  portable

    This module implements a type for representing source file edits,
    primarily to provide quick fixes in language tooling.
-}
module Curry.Base.TextEdit
  ( TextEdit (..), insertEdit, replaceEdit
  ) where

import Curry.Base.Span (Span (..))
import Curry.Base.Position (Position (..), next)

-- |A source file edit.
data TextEdit = TextEdit
  { editStart :: Position -- ^ The (inclusive) start of the range to replace
  , editEnd   :: Position -- ^ The (exclusive) end of the range to replace
  , editText  :: String   -- ^ The text to replace the span with
  }
  deriving (Eq, Ord, Show)

-- |Creates an edit that inserts at the given position the given text.
insertEdit :: Position -> String -> TextEdit
insertEdit p = TextEdit p p

-- |Creates an edit that replaces the given span with the given text.
replaceEdit :: Span -> String -> TextEdit
replaceEdit sp = TextEdit p1 p2
  where p1 = start sp
        p2 = next (end sp)
