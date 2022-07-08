{- |
    Module      :  $Header$
    Description :  Curry language extensions
    Copyright   :  (c) 2013 - 2014 Björn Peemöller
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the data structures for Curry language extensions.
-}

module Curry.Syntax.Extension
  ( -- * Extensions
    Extension (..), KnownExtension (..), classifyExtension, kielExtensions
    -- * Tools
  , Tool (..), classifyTool
  ) where

import Data.Binary
import Data.Char           (toUpper)
import Control.Monad

import Curry.Base.Ident    (Ident (..))
import Curry.Base.Position
import Curry.Base.SpanInfo

-- |Specified language extensions, either known or unknown.
data Extension
  = KnownExtension   SpanInfo KnownExtension -- ^ a known extension
  | UnknownExtension SpanInfo String         -- ^ an unknown extension
    deriving (Eq, Read, Show)

instance HasSpanInfo Extension where
  getSpanInfo (KnownExtension   spi _) = spi
  getSpanInfo (UnknownExtension spi _) = spi
  
  setSpanInfo spi (KnownExtension   _ ke) = KnownExtension spi ke
  setSpanInfo spi (UnknownExtension _ s)  = UnknownExtension spi s

instance HasPosition Extension where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance Binary Extension where
  put (KnownExtension   p e) = putWord8 0 >> put p >> put e
  put (UnknownExtension p e) = putWord8 1 >> put p >> put e

  get = do
    x <- getWord8
    case x of
      0 -> liftM2 KnownExtension get get
      1 -> liftM2 UnknownExtension get get
      _ -> fail "Invalid encoding for Extension"

instance Binary KnownExtension where
  put AnonFreeVars       = putWord8 0
  put CPP                = putWord8 1
  put FunctionalPatterns = putWord8 2
  put NegativeLiterals   = putWord8 3
  put NoImplicitPrelude  = putWord8 4
  put NoDataDeriving     = putWord8 5

  get = do
    x <- getWord8
    case x of
      0 -> return AnonFreeVars
      1 -> return CPP
      2 -> return FunctionalPatterns
      3 -> return NegativeLiterals
      4 -> return NoImplicitPrelude
      5 -> return NoDataDeriving
      _ -> fail "Invalid encoding for KnownExtension"

-- |Known language extensions of Curry.
data KnownExtension
  = AnonFreeVars              -- ^ anonymous free variables
  | CPP                       -- ^ C preprocessor
  | FunctionalPatterns        -- ^ functional patterns
  | NegativeLiterals          -- ^ negative literals
  | NoImplicitPrelude         -- ^ no implicit import of the prelude
  | NoDataDeriving            -- ^ no implicit deriving of the Data class
    deriving (Eq, Read, Show, Enum, Bounded)

-- |Classifies a 'String' as an 'Extension'
classifyExtension :: Ident -> Extension
classifyExtension i = case reads extName of
  [(e, "")] -> KnownExtension   (getSpanInfo i) e
  _         -> UnknownExtension (getSpanInfo i) extName
  where extName = idName i

-- |'Extension's available by Kiel's Curry compilers.
kielExtensions :: [KnownExtension]
kielExtensions = [AnonFreeVars, FunctionalPatterns]

-- |Different Curry tools which may accept compiler options.
data Tool = KICS2 | PAKCS | CYMAKE | FRONTEND | UnknownTool String
    deriving (Eq, Read, Show)

instance Binary Tool where
  put KICS2           = putWord8 0
  put PAKCS           = putWord8 1
  put CYMAKE          = putWord8 2
  put FRONTEND        = putWord8 3
  put (UnknownTool s) = putWord8 4 >> put s

  get = do
    x <- getWord8
    case x of
      0 -> return KICS2
      1 -> return PAKCS
      2 -> return CYMAKE
      3 -> return FRONTEND
      4 -> fmap UnknownTool get
      _ -> fail "Invalid encoding for Tool"

-- |Classifies a 'String' as a 'Tool'
classifyTool :: String -> Tool
classifyTool str = case reads (map toUpper str) of
  [(t, "")] -> t
  _         -> UnknownTool str
