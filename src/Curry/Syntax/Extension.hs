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
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
module Curry.Syntax.Extension
  ( -- * Extensions
    Extension (..), KnownExtension (..), classifyExtension, kielExtensions
    -- * Tools
  , Tool (..), KnownTool (..), classifyTool
  ) where

import Data.Binary
import Data.Char           (toUpper)
import GHC.Generics

import Curry.Base.Ident    (Ident (..))
import Curry.Base.Position
import Curry.Base.SpanInfo

-- |Specified language extensions, either known or unknown.
data Extension
  = KnownExtension   SpanInfo KnownExtension -- ^ a known extension
  | UnknownExtension SpanInfo String         -- ^ an unknown extension
    deriving (Eq, Read, Show, Generic, Binary)

instance HasSpanInfo Extension where
  getSpanInfo (KnownExtension   spi _) = spi
  getSpanInfo (UnknownExtension spi _) = spi

  setSpanInfo spi (KnownExtension   _ ke) = KnownExtension spi ke
  setSpanInfo spi (UnknownExtension _ s)  = UnknownExtension spi s

instance HasPosition Extension where
  getPosition = getStartPosition
  setPosition = setStartPosition

-- |Known language extensions of Curry.
data KnownExtension
  = AnonFreeVars              -- ^ anonymous free variables
  | CPP                       -- ^ C preprocessor
  | FunctionalPatterns        -- ^ functional patterns
  | NegativeLiterals          -- ^ negative literals
  | NoAnonFreeVars            -- ^ no anonymous free variables
  | NoFunctionalPatterns      -- ^ no functional patterns
  | NoImplicitPrelude         -- ^ no implicit import of the prelude
  | NoDataDeriving            -- ^ no implicit deriving of the Data class
    deriving (Eq, Ord, Read, Show, Enum, Bounded, Generic, Binary)

-- |Classifies a 'String' as an 'Extension'
classifyExtension :: Ident -> Extension
classifyExtension i = case reads extName of
  [(e, "")] -> KnownExtension   (getSpanInfo i) e
  _         -> UnknownExtension (getSpanInfo i) extName
  where extName = idName i

-- |'Extension's available by Kiel's Curry compilers.
kielExtensions :: [KnownExtension]
kielExtensions = [AnonFreeVars, FunctionalPatterns]

-- |Known Curry tools which may accept compiler options.
-- Note: CYMAKE is kept for legacy/compatibility reasons
--       and is deprecated, specify options for FRONTEND instead.
data KnownTool = KICS2 | PAKCS | CYMAKE | FRONTEND
    deriving (Eq, Read, Show, Enum, Bounded, Generic, Binary)

-- |Different Curry tools which may accept compiler options.
data Tool = KnownTool KnownTool | UnknownTool String
    deriving (Eq, Read, Show, Generic, Binary)

-- |Classifies a 'String' as a 'Tool'
classifyTool :: String -> Tool
classifyTool str = case reads (map toUpper str) of
  [(t, "")] -> KnownTool t
  _         -> UnknownTool str
