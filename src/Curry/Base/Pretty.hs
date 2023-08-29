{- |
    Module      :  $Header$
    Description :  Pretty printing
    Copyright   :  (c) 2013 - 2014 Björn Peemöller
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  stable
    Portability :  portable

    This module re-exports the well known pretty printing combinators
    from Hughes and Peyton-Jones. In addition, it re-exports the type class
    'Pretty' for pretty printing arbitrary types.
-}
{-# LANGUAGE CPP #-}
module Curry.Base.Pretty
  ( module Curry.Base.Pretty
  , module Text.PrettyPrint
  ) where

import Prelude hiding ((<>))
import qualified Data.Set as Set

import Text.PrettyPrint

-- | Pretty printing class.
-- The precedence level is used in a similar way as in the 'Show' class.
-- Minimal complete definition is either 'pPrintPrec' or 'pPrint'.
class Pretty a where
  {-# MINIMAL pPrintPrec | pPrint #-}
  -- | Pretty-print something in isolation.
  pPrint :: a -> Doc
  pPrint = pPrintPrec 0

  -- | Pretty-print something in a precedence context.
  pPrintPrec :: Int -> a -> Doc
  pPrintPrec _ = pPrint

  -- |Pretty-print a list.
  pPrintList :: [a] -> Doc
  pPrintList = brackets . fsep . punctuate comma . map (pPrintPrec 0)

instance Pretty a => Pretty (Set.Set a) where
  pPrint = parens . list . map pPrint . Set.toAscList

-- | Pretty print a value to a 'String'.
prettyShow :: Pretty a => a -> String
prettyShow = render . pPrint

-- | Parenthesize an value if the boolean is true.
parenIf :: Bool -> Doc -> Doc
parenIf False = id
parenIf True  = parens

-- | Pretty print a value if the boolean is true
ppIf :: Bool -> Doc -> Doc
ppIf True  = id
ppIf False = const empty

-- | Pretty print a 'Maybe' value for the 'Just' constructor only
maybePP :: (a -> Doc) -> Maybe a -> Doc
maybePP = maybe empty

-- | A blank line.
blankLine :: Doc
blankLine = text ""

-- |Above with a blank line in between. If one of the documents is empty,
-- then the other document is returned.
($++$) :: Doc -> Doc -> Doc
d1 $++$ d2 | isEmpty d1 = d2
           | isEmpty d2 = d1
           | otherwise  = d1 $+$ blankLine $+$ d2

-- |Above with overlapping, but with a space in between. If one of the
-- documents is empty, then the other document is returned.
($-$) :: Doc -> Doc -> Doc
d1 $-$ d2 | isEmpty d1 = d2
          | isEmpty d2 = d1
          | otherwise  = d1 $$ space $$ d2

-- | Seperate a list of 'Doc's by a 'blankLine'.
sepByBlankLine :: [Doc] -> Doc
sepByBlankLine = foldr ($++$) empty

-- |A '.' character.
dot :: Doc
dot = char '.'

-- |Precedence of function application
appPrec :: Int
appPrec = 10

-- |A left arrow @<-@.
larrow :: Doc
larrow = text "<-"

-- |A right arrow @->@.
rarrow :: Doc
rarrow = text "->"

-- |A double arrow @=>@.
darrow :: Doc
darrow = text "=>"

-- |A back quote @`@.
backQuote :: Doc
backQuote = char '`'

-- |A backslash @\@.
backsl :: Doc
backsl = char '\\'

-- |A vertical bar @|@.
vbar :: Doc
vbar = char '|'

-- |Set a document in backquotes.
bquotes :: Doc -> Doc
bquotes doc = backQuote <> doc <> backQuote

-- |Set a document in backquotes if the condition is @True@.
bquotesIf :: Bool -> Doc -> Doc
bquotesIf b doc = if b then bquotes doc else doc

-- |Seperate a list of documents by commas
list :: [Doc] -> Doc
list = fsep . punctuate comma . filter (not . isEmpty)

-- | Instance for 'Int'
instance Pretty Int      where pPrint = int

-- | Instance for 'Integer'
instance Pretty Integer  where pPrint = integer

-- | Instance for 'Float'
instance Pretty Float    where pPrint = float

-- | Instance for 'Double'
instance Pretty Double   where pPrint = double

-- | Instance for '()'
instance Pretty ()       where pPrint _ = text "()"

-- | Instance for 'Bool'
instance Pretty Bool     where pPrint = text . show

-- | Instance for 'Ordering'
instance Pretty Ordering where pPrint = text . show

-- | Instance for 'Char'
instance Pretty Char where
  pPrint     = char
  pPrintList = text . show

-- | Instance for 'Maybe'
instance (Pretty a) => Pretty (Maybe a) where
  pPrintPrec _ Nothing  = text "Nothing"
  pPrintPrec p (Just x) = parenIf (p > appPrec)
                        $ text "Just" <+> pPrintPrec (appPrec + 1) x

-- | Instance for 'Either'
instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pPrintPrec p (Left  x) = parenIf (p > appPrec)
                         $ text "Left" <+> pPrintPrec (appPrec + 1) x
  pPrintPrec p (Right x) = parenIf (p > appPrec)
                         $ text "Right" <+> pPrintPrec (appPrec + 1) x

-- | Instance for '[]'
instance (Pretty a) => Pretty [a] where
  pPrintPrec _ = pPrintList

-- | Instance for '(,)'
instance (Pretty a, Pretty b) => Pretty (a, b) where
  pPrintPrec _ (a, b) = parens $ fsep $ punctuate comma [pPrint a, pPrint b]

-- | Instance for '(,,)'
instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  pPrintPrec _ (a, b, c) = parens $ fsep $ punctuate comma
    [pPrint a, pPrint b, pPrint c]

-- | Instance for '(,,,)'
instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty (a, b, c, d) where
  pPrintPrec _ (a, b, c, d) = parens $ fsep $ punctuate comma
    [pPrint a, pPrint b, pPrint c, pPrint d]

-- | Instance for '(,,,,)'
instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e)
  => Pretty (a, b, c, d, e) where
  pPrintPrec _ (a, b, c, d, e) = parens $ fsep $ punctuate comma
    [pPrint a, pPrint b, pPrint c, pPrint d, pPrint e]

-- | Instance for '(,,,,,)'
instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e, Pretty f)
  => Pretty (a, b, c, d, e, f) where
  pPrintPrec _ (a, b, c, d, e, f) = parens $ fsep $ punctuate comma
    [pPrint a, pPrint b, pPrint c, pPrint d, pPrint e, pPrint f]

-- | Instance for '(,,,,,,)'
instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e, Pretty f, Pretty g)
  => Pretty (a, b, c, d, e, f, g) where
  pPrintPrec _ (a, b, c, d, e, f, g) = parens $ fsep $ punctuate comma
    [pPrint a, pPrint b, pPrint c, pPrint d, pPrint e, pPrint f, pPrint g]

-- | Instance for '(,,,,,,,)'
instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e, Pretty f, Pretty g, Pretty h)
  => Pretty (a, b, c, d, e, f, g, h) where
  pPrintPrec _ (a, b, c, d, e, f, g, h) = parens $ fsep $ punctuate comma
    [pPrint a, pPrint b, pPrint c, pPrint d, pPrint e, pPrint f, pPrint g, pPrint h]
