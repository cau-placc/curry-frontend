{- |
    Module      :  $Header$
    Description :  Conversion of kind representation
    Copyright   :  (c) 2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The functions 'tokind' and 'fromKind' convert Curry kind expressions into
   kinds and vice versa.

   When Curry kinds are converted with 'fromKind', kind variables are
   instantiated with the kind *.
-}

module Base.CurryKinds
  ( toKind, toKind', toClassKind, fromKind, fromKind', fromClassKind, ppKind
  ) where

import Curry.Base.Pretty (Doc)
import Curry.Syntax.Pretty (pPrintPrec)
import Curry.Syntax.Type (KindExpr (..))

import Base.Kinds

toKind :: KindExpr -> Kind
toKind Star              = KindStar
toKind ConstraintKind    = KindConstraint
toKind (ArrowKind k1 k2) = KindArrow (toKind k1) (toKind k2)

toKind' :: Maybe KindExpr -> Int -> Kind
toKind' k n = maybe (simpleKind n) toKind k

toClassKind :: Maybe KindExpr -> Int -> Kind
toClassKind k n = maybe (simpleClassKind n) toKind k

fromKind :: Kind -> KindExpr
fromKind KindStar          = Star
fromKind KindConstraint    = ConstraintKind
fromKind (KindVariable  _) = Star
fromKind (KindArrow k1 k2) = ArrowKind (fromKind k1) (fromKind k2)

fromKind' :: Kind -> Int -> Maybe KindExpr
fromKind' k n | k == simpleKind n = Nothing
              | otherwise         = Just (fromKind k)

fromClassKind :: Kind -> Int -> Maybe KindExpr
fromClassKind k n | k == simpleClassKind n = Nothing
                  | otherwise              = Just (fromKind k)

ppKind :: Kind -> Doc
ppKind = pPrintPrec 0 . fromKind
