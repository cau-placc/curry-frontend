{- |
    Module      :  $Header$
    Description :  Spans in a source file
    Copyright   :  (c) 2016 Jan Tikovsky
                       2016 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  jrt@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements a data type for span information in a source file and
    respective functions to operate on them. A source file span consists
    of a filename, a start position and an end position.

    In addition, the type 'SrcRef' identifies the path to an expression in
    the abstract syntax tree by argument positions, which is used for
    debugging purposes.
-}
module Curry.Base.Span where

import Prelude hiding ((<>))

import Data.Binary
import Data.List (transpose)
import Control.Monad
import System.FilePath

import Curry.Base.Position hiding (file)
import Curry.Base.Pretty

data Span
  -- |Normal source code span
  = Span
    { file     :: FilePath -- ^ 'FilePath' of the source file
    , start    :: Position -- ^ start position
    , end      :: Position -- ^ end position
    }
  -- |no span
  | NoSpan
    deriving (Eq, Ord, Read, Show)

instance Pretty Span where
  pPrint = ppSpan

instance HasPosition Span where
  setPosition p NoSpan       = Span "" p NoPos
  setPosition p (Span f _ e) = Span f p e

  getPosition NoSpan       = NoPos
  getPosition (Span _ p _) = p

instance Binary Span where
  put (Span _ s e) = putWord8 0 >> put s >> put e
  put NoSpan       = putWord8 1

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 (Span "") get get
      1 -> return NoSpan
      _ -> fail "Not a valid encoding for a Span"

-- |Show a 'Span' as a 'String'
showSpan :: Span -> String
showSpan = show . ppSpan

-- |Pretty print a 'Span'
ppSpan :: Span -> Doc
ppSpan s@(Span f _ _)
  | null f    = startEnd
  | otherwise = text (normalise f) <> comma <+> startEnd
  where startEnd = ppPositions s
ppSpan _ = empty

-- |Pretty print a span with it's file path and position compactly.
ppCompactSpan :: Span -> Doc
ppCompactSpan s@(Span f _ _)
  | null f    = ppCompactPositions s
  | otherwise = text (normalise f) <> colon <> ppCompactPositions s
ppCompactSpan _ = empty

-- |Pretty print a source preview of a span
ppSpanPreview :: Span -> IO Doc
ppSpanPreview (Span f (Position _ sl sc) (Position _ el ec))
  | null f    = return empty
  | otherwise = do
      fileContents <- readFile f

      let lnContent = lines fileContents !! (sl - 1)
          lnNum = text <$> lPadStr lnNumWidth <$> (vPad ++ [show sl] ++ vPad)
          ec' = if isMultiline then length lnContent else ec
          gutter = text <$> replicate (1 + 2 * vPadCount) "|"
          highlight = replicate (sc - 1) ' ' ++ replicate (1 + ec' - sc) '^' ++ if isMultiline then "..." else ""
          previews = text <$> (vPad ++ [lnContent, highlight] ++ replicate (vPadCount - 1) "")
      
      return $ vcat $ map hsep $ transpose [lnNum, gutter, previews]
  where vPadCount = 1 -- Number of padding lines at the top and bottom
        isMultiline = el - sl > 0
        numWidth = length . show
        lnNumWidth = 1 + numWidth el
        vPad = replicate vPadCount ""
        lPadStr n s = replicate (n - length s) ' ' ++ s
ppSpanPreview _ = return empty

-- |Pretty print the positions compactly.
ppCompactPositions :: Span -> Doc
ppCompactPositions (Span _ s e) | s == e    = ppCompactLine s
                                | otherwise = ppCompactLine s <> text "-" <> ppCompactLine e
ppCompactPositions _            = empty

-- |Pretty print the start and end position of a 'Span'
ppPositions :: Span -> Doc
ppPositions (Span _ s e) =  text "startPos:" <+> ppLine s <> comma
                        <+> text "endPos:"   <+> ppLine e
ppPositions _            = empty

fstSpan :: FilePath -> Span
fstSpan fn = Span fn (first fn) (first fn)

-- |Compute the column of the start position of a 'Span'
startCol :: Span -> Int
startCol (Span _ p _) = column p
startCol _            = 0

nextSpan :: Span -> Span
nextSpan sp = incrSpan sp 1

incrSpan :: Span -> Int -> Span
incrSpan (Span fn s e) n = Span fn (incr s n) (incr e n)
incrSpan sp            _ = sp

-- TODO: Rename to tab and nl as soon as positions are completely replaced by spans

-- |Convert a position to a single character span.
pos2Span :: Position -> Span
pos2Span p@(Position f _ _) = Span f p p
pos2Span _                  = NoSpan

-- |Convert a span to a (start) position
-- TODO: This function should be removed as soon as positions are completely replaced by spans
-- in the frontend
span2Pos :: Span -> Position
span2Pos (Span _ p _) = p
span2Pos NoSpan       = NoPos

combineSpans :: Span -> Span -> Span
combineSpans sp1 sp2 = Span f s e
  where s = start sp1
        e = end sp2
        f = file sp1

-- |First position after the next tabulator
tabSpan :: Span -> Span
tabSpan (Span fn s e) = Span fn (tab s) (tab e)
tabSpan sp            = sp

-- |First position of the next line
nlSpan :: Span -> Span
nlSpan (Span fn s e) = Span fn (nl s) (nl e)
nlSpan sp            = sp

addSpan :: Span -> (a, [Span]) -> (a, [Span])
addSpan sp (a, ss) = (a, sp:ss)

-- |Distance of a span, i.e. the line and column distance between start
-- and end position
type Distance = (Int, Int)

-- |Set the distance of a span, i.e. update its end position
setDistance :: Span -> Distance -> Span
setDistance (Span fn p _) d = Span fn p (p `moveBy` d)
setDistance s             _ = s

-- |Move position by given distance
moveBy :: Position -> Distance -> Position
moveBy (Position fn l c) (ld, cd) = Position fn (l + ld) (c + cd)
moveBy p                 _        = p
