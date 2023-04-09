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
  , impliedExtensions, impliedClosure
    -- * Tools
  , Tool (..), classifyTool
  ) where

import qualified Data.Set.Extra as Set
import Control.Monad
import qualified Data.Set as Set

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
  | FunctionalDependencies    -- ^ functional dependencies
  | FunctionalPatterns        -- ^ functional patterns
  | MultiParamTypeClasses     -- ^ multi-parameter type classes
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

-- |Extensions implied by the given extension.
impliedExtensions :: KnownExtension -> Set.Set KnownExtension
impliedExtensions NoImplicitPrelude = Set.singleton NoDataDeriving
impliedExtensions _                 = Set.empty

-- |Extensions implied (possibly transitively) by the given extensions.
impliedClosure :: Set.Set KnownExtension -> Set.Set KnownExtension
impliedClosure exts | exts == exts' = exts
                    | otherwise     = impliedClosure exts'
  where exts' = Set.union exts $ Set.concatMap impliedExtensions exts

-- |Different Curry tools which may accept compiler options.
data Tool = KICS2 | PAKCS | CYMAKE | FRONTEND | UnknownTool String
    deriving (Eq, Read, Show, Generic, Binary)

-- |Classifies a 'String' as a 'Tool'
classifyTool :: String -> Tool
classifyTool str = case reads (map toUpper str) of
  [(t, "")] -> t
  _         -> UnknownTool str
