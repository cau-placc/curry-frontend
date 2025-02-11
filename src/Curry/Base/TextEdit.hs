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
  ( TextEdit (..)
  ) where

import Curry.Base.Span (Span (..))

-- |A source file edit.
data TextEdit = TextEdit
  { editStart :: Position -- ^ The (inclusive) start of the range to replace
  , editEnd   :: Position -- ^ The (exclusive) end of the range to replace
  , editText  :: String   -- ^ The text to replace the span with
  }
  deriving (Eq, Ord, Show)
