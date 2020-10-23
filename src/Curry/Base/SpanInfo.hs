{- |
    Module      :  $Header$
    Description :  SpansInfo for entities
    Copyright   :  (c) 2017 Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements a data type for span information for entities from a
    source file and function to operate on them. A span info consists of the
    span of the entity and a list of sub-spans whith additional information
    about location of keywords, e.g.
-}
module Curry.Base.SpanInfo
  ( SpanInfo(..), spanInfo, LayoutInfo(..), HasSpanInfo(..)
  , fromSrcSpan, fromSrcSpanBoth, getSrcSpan, setSrcSpan, spanInfoLike
  , fromSrcInfoPoints, getSrcInfoPoints, setSrcInfoPoints
  , getStartPosition, getSrcSpanEnd, setStartPosition, setEndPosition
  , spanInfo2Pos
  ) where

import Data.Binary
import Control.Monad

import Curry.Base.Position
import Curry.Base.Span

data SpanInfo = SpanInfo
    { srcSpan        :: Span
    , srcInfoPoints  :: [Span]
    }
    | NoSpanInfo
  deriving (Eq, Ord, Read, Show)

spanInfo :: Span -> [Span] -> SpanInfo
spanInfo sp sps = SpanInfo sp sps

data LayoutInfo = ExplicitLayout [Span]
                | WhitespaceLayout
  deriving (Eq, Read, Show)

class HasPosition a => HasSpanInfo a where

  getSpanInfo :: a -> SpanInfo

  setSpanInfo :: SpanInfo -> a -> a

  updateEndPos :: a -> a
  updateEndPos = id

  getLayoutInfo :: a -> LayoutInfo
  getLayoutInfo = const WhitespaceLayout

instance HasSpanInfo SpanInfo where
  getSpanInfo = id
  setSpanInfo = const

instance HasPosition SpanInfo where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance Binary SpanInfo where
  put (SpanInfo sp ss) = putWord8 0 >> put sp >> put ss
  put NoSpanInfo       = putWord8 1

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 SpanInfo get get
      1 -> return NoSpanInfo
      _ -> fail "Not a valid encoding for a SpanInfo"

instance Binary LayoutInfo where
  put (ExplicitLayout ss) = putWord8 0 >> put ss
  put WhitespaceLayout = putWord8 1

  get = do
    x <- getWord8
    case x of
      0 -> fmap ExplicitLayout get
      1 -> return WhitespaceLayout
      _ -> fail "Not a valid encoding for a LayoutInfo"

fromSrcSpan :: Span -> SpanInfo
fromSrcSpan sp = SpanInfo sp []

fromSrcSpanBoth :: Span -> SpanInfo
fromSrcSpanBoth sp = SpanInfo sp [sp]

getSrcSpan :: HasSpanInfo a => a -> Span
getSrcSpan a = case getSpanInfo a of
  NoSpanInfo   -> NoSpan
  SpanInfo s _ -> s

setSrcSpan :: HasSpanInfo a => Span -> a -> a
setSrcSpan s a = case getSpanInfo a of
  NoSpanInfo     -> setSpanInfo (SpanInfo s [] ) a
  SpanInfo _ inf -> setSpanInfo (SpanInfo s inf) a

fromSrcInfoPoints :: [Span] -> SpanInfo
fromSrcInfoPoints = SpanInfo NoSpan

getSrcInfoPoints :: HasSpanInfo a => a -> [Span]
getSrcInfoPoints a = case getSpanInfo a of
  NoSpanInfo    -> []
  SpanInfo _ xs -> xs

setSrcInfoPoints :: HasSpanInfo a => [Span] -> a -> a
setSrcInfoPoints inf a = case getSpanInfo a of
  NoSpanInfo    -> setSpanInfo (SpanInfo NoSpan inf) a
  SpanInfo s _  -> setSpanInfo (SpanInfo s      inf) a

getStartPosition :: HasSpanInfo a => a -> Position
getStartPosition a =  case getSrcSpan a of
  NoSpan     -> NoPos
  Span _ s _ -> s

getSrcSpanEnd :: HasSpanInfo a => a -> Position
getSrcSpanEnd a = case getSpanInfo a of
  NoSpanInfo   -> NoPos
  SpanInfo s _ -> end s

setStartPosition :: HasSpanInfo a => Position -> a -> a
setStartPosition p a = case getSrcSpan a of
  NoSpan     -> setSrcSpan (Span "" p NoPos) a
  Span f _ e -> setSrcSpan (Span f  p     e) a

setEndPosition :: HasSpanInfo a => Position -> a -> a
setEndPosition e a = case getSrcSpan a of
  NoSpan     -> setSrcSpan (Span "" NoPos e) a
  Span f p _ -> setSrcSpan (Span f  p     e) a

spanInfo2Pos :: HasSpanInfo a => a -> Position
spanInfo2Pos = getStartPosition

spanInfoLike :: (HasSpanInfo a, HasSpanInfo b) => a -> b -> a
spanInfoLike a b = setSpanInfo (getSpanInfo b) a
