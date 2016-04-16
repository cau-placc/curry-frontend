{- |
    Module      :  $Header$
    Description :  Conversion of kind representation
    Copyright   :  (c) 2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The functions 'tokind' and 'fromKind' convert Curry kind expressions into
   kinds and vice versa.

   When Curry kinds are converted with 'fromKind', kind variables are
   instantiated with the kind *.
-}

module Base.CurryKinds
  ( toKind, fromKind, ppKind
  ) where

import Curry.Base.Pretty (Doc)
import Curry.Syntax.Pretty (ppKindExpr)
import Curry.Syntax.Type (KindExpr (..))

import Base.Kinds

toKind :: KindExpr -> Kind
toKind Star              = KindStar
toKind (ArrowKind k1 k2) = KindArrow (toKind k1) (toKind k2)

fromKind :: Kind -> KindExpr
fromKind KindStar          = Star
fromKind (KindVariable  _) = Star
fromKind (KindArrow k1 k2) = ArrowKind (fromKind k1) (fromKind k2)

ppKind :: Kind -> Doc
ppKind = ppKindExpr 0 . fromKind
