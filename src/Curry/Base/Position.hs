{- |
    Module      :  $Header$
    Description :  Positions in a source file
    Copyright   :  (c) Wolfgang Lux
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements a data type for positions in a source file and
    respective functions to operate on them. A source file position consists
    of a filename, a line number, and a column number. A tab stop is assumed
    at every eighth column.
-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
module Curry.Base.Position
  ( -- * Source code position
    HasPosition (..), Position (..), (@>)
  , showPosition, ppPosition, ppCompactLine, ppLine, showLine
  , first, next, incr, tab, tabWidth, nl
  ) where

import Data.Binary
import GHC.Generics
import Prelude hiding ((<>))
import System.FilePath

import Curry.Base.Pretty

-- |Type class for entities which have a source code 'Position'
class HasPosition a where
  -- |Get the 'Position'
  getPosition :: a -> Position
  getPosition _ = NoPos

  -- |Set the 'Position'
  setPosition :: Position -> a -> a
  setPosition _ = id

-- | @x \@> y@ returns @x@ with the position obtained from @y@
(@>) :: (HasPosition a, HasPosition b) => a -> b -> a
x @> y = setPosition (getPosition y) x

-- |Source code positions
data Position
  -- |Normal source code position
  = Position
    { file   :: FilePath -- ^ 'FilePath' of the source file
    , line   :: Int      -- ^ line number, beginning at 1
    , column :: Int      -- ^ column number, beginning at 1
    }
  -- |no position
  | NoPos
    deriving (Eq, Ord, Read, Show, Generic, Binary)

instance HasPosition Position where
  getPosition = id
  setPosition = const

instance Pretty Position where
  pPrint = ppPosition

-- |Show a 'Position' as a 'String'
showPosition :: Position -> String
showPosition = show . ppPosition

-- |Pretty print a 'Position'
ppPosition :: Position -> Doc
ppPosition p@(Position f _ _)
  | null f    = lineCol
  | otherwise = text (normalise f) <> comma <+> lineCol
  where lineCol = ppLine p
ppPosition _  = empty

-- |Pretty print a compact representation of a 'Position''s line/column
ppCompactLine :: Position -> Doc
ppCompactLine (Position _ l c) = text (show l)
                                 <> if c == 0 then empty else colon <> text (show c)
ppCompactLine _ = empty

-- |Pretty print the line and column of a 'Position'
ppLine :: Position -> Doc
ppLine (Position _ l c) = text "line" <+> text (show l)
                          <> if c == 0 then empty else text ('.' : show c)
ppLine _                = empty

-- |Show the line and column of a 'Position'
showLine :: Position -> String
showLine = show . ppLine

-- | Absolute first position of a file
first :: FilePath -> Position
first fn = Position fn 1 1

-- |Next position to the right
next :: Position -> Position
next = flip incr 1

-- |Increment a position by a number of columns
incr :: Position -> Int -> Position
incr p@Position { column = c } n = p { column = c + n }
incr p _ = p

-- |Number of spaces for a tabulator
tabWidth :: Int
tabWidth = 8

-- |First position after the next tabulator
tab :: Position -> Position
tab p@Position { column = c }
  = p { column = c + tabWidth - (c - 1) `mod` tabWidth }
tab p = p

-- |First position of the next line
nl :: Position -> Position
nl p@Position { line = l } = p { line = l + 1, column = 1 }
nl p = p
