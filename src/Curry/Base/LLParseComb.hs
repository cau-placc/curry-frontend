{- |
    Module      :  $Header$
    Description :  Parser combinators
    Copyright   :  (c) 1999-2004, Wolfgang Lux
                       2016     , Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The parsing combinators implemented in this module are based on the
    LL(1) parsing combinators developed by Swierstra and Duponcheel.
    They have been adapted to using continuation passing style in order to
    work with the lexing combinators described in the previous section.
    In addition, the facilities for error correction are omitted
    in this implementation.

    The two functions 'applyParser' and 'prefixParser' use the specified
    parser for parsing a string. When 'applyParser' is used, an error is
    reported if the parser does not consume the whole string,
    whereas 'prefixParser' discards the rest of the input string in this case.
-}
{-# LANGUAGE CPP #-}

module Curry.Base.LLParseComb
  ( -- * Data types
    Parser

    -- * Parser application
  , fullParser, prefixParser

    -- * Basic parsers
  , position, spanPosition, succeed, failure, symbol

    -- *  parser combinators
  , (<?>), (<|>), (<|?>), (<*>), (<\>), (<\\>)
  , (<$>), (<$->), (<*->), (<-*>), (<**>), (<??>), (<.>)
  , opt, choice, flag, optional, option, many, many1, sepBy, sepBy1
  , sepBySp, sepBy1Sp
  , chainr, chainr1, chainl, chainl1, between, ops

    -- * Layout combinators
  , layoutOn, layoutOff, layoutEnd
  ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (Applicative, (<*>), (<$>), pure)
#endif
import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Curry.Base.LexComb
import Curry.Base.Position
import Curry.Base.Span (span2Pos, Span, startCol, setDistance)

infixl 5 <\>, <\\>
infixl 4 <$->, <*->, <-*>, <**>, <??>, <.>
infixl 3 <|>, <|?>
infixl 2 <?>, `opt`

-- ---------------------------------------------------------------------------
-- Parser types
-- ---------------------------------------------------------------------------

-- |Parsing function
type ParseFun a s b  = (b -> SuccessP s a) -> FailP a -> SuccessP s a

-- |CPS-Parser type
data Parser a s b = Parser
  -- Parsing function for empty word
  (Maybe (ParseFun a s b))
  -- Lookup table (continuations for 'Symbol's recognized by the parser)
  (Map.Map s (Lexer s a -> ParseFun a s b))

instance Symbol s => Functor (Parser a s) where
  fmap f p = succeed f <*> p

instance Symbol s => Applicative (Parser a s) where
  pure = succeed

  -- |Apply the result function of the first parser to the result of the
  --  second parser.
  Parser Nothing   ps1 <*> p2                  = Parser Nothing
    (fmap (`seqPP` p2) ps1)
  Parser (Just p1) ps1 <*> ~p2@(Parser e2 ps2) = Parser (fmap (seqEE p1) e2)
    (Map.union (fmap (`seqPP` p2) ps1) (fmap (seqEP p1) ps2))

instance Show s => Show (Parser a s b) where
  showsPrec p (Parser e ps) = showParen (p >= 10) $
    showString "Parser " . shows (isJust e) .
    showChar ' ' . shows (Map.keysSet ps)

-- ---------------------------------------------------------------------------
-- Parser application
-- ---------------------------------------------------------------------------

-- |Apply a parser and lexer to a 'String', whereas the 'FilePath' is used
-- to identify the origin of the 'String' in case of parsing errors.
fullParser :: Symbol s => Parser a s a -> Lexer s a -> FilePath -> String
           -> CYM a
fullParser p lexer = parse (lexer (choose p lexer successP failP) failP)
  where successP x pos s
          | isEOF s   = returnP x
          | otherwise = failP pos (unexpected s)

-- |Apply a parser and lexer to parse the beginning of a 'String'.
-- The 'FilePath' is used to identify the origin of the 'String' in case of
-- parsing errors.
prefixParser :: Symbol s => Parser a s a -> Lexer s a -> FilePath -> String
             -> CYM a
prefixParser p lexer = parse (lexer (choose p lexer discardP failP) failP)
  where discardP x _ _ = returnP x

-- |Choose the appropriate parsing function w.r.t. to the next 'Symbol'.
choose :: Symbol s => Parser a s b -> Lexer s a -> ParseFun a s b
choose (Parser e ps) lexer success failp pos s = case Map.lookup s ps of
  Just p  -> p lexer success failp pos s
  Nothing -> case e of
    Just p  -> p success failp pos s
    Nothing -> failp pos (unexpected s)

-- |Fail on an unexpected 'Symbol'
unexpected :: Symbol s => s -> String
unexpected s
  | isEOF s   = "Unexpected end-of-file"
  | otherwise = "Unexpected token " ++ show s

-- ---------------------------------------------------------------------------
-- Basic parsers
-- ---------------------------------------------------------------------------

-- |Return the current position without consuming the input
position :: Parser a s Position
position = Parser (Just p) Map.empty
  where p success _ sp = success (span2Pos sp) sp

spanPosition :: Symbol s => Parser a s Span
spanPosition = Parser (Just p) Map.empty
  where p success _ sp s = success (setDistance sp (dist (startCol sp) s)) sp s

-- |Always succeeding parser
succeed :: b -> Parser a s b
succeed x = Parser (Just p) Map.empty
  where p success _ = success x

-- |Always failing parser with a given message
failure :: String -> Parser a s b
failure msg = Parser (Just p) Map.empty
  where p _ failp pos _ = failp pos msg

-- |Create a parser accepting the given 'Symbol'
symbol :: s -> Parser a s s
symbol s = Parser Nothing (Map.singleton s p)
  where p lexer success failp _ s' = lexer (success s') failp

-- ---------------------------------------------------------------------------
-- Parser combinators
-- ---------------------------------------------------------------------------

-- |Behave like the given parser, but use the given 'String' as the error
-- message if the parser fails
(<?>) :: Symbol s => Parser a s b -> String -> Parser a s b
p <?> msg = p <|> failure msg

-- |Deterministic choice between two parsers.
-- The appropriate parser is chosen based on the next 'Symbol'
(<|>) :: Symbol s => Parser a s b -> Parser a s b -> Parser a s b
Parser e1 ps1 <|> Parser e2 ps2
  | isJust e1 && isJust e2 = failure "Ambiguous parser for empty word"
  | not (Set.null common)  = failure $ "Ambiguous parser for " ++ show common
  | otherwise              = Parser (e1 `mplus` e2) (Map.union ps1 ps2)
  where common = Map.keysSet ps1 `Set.intersection` Map.keysSet ps2

-- |Non-deterministic choice between two parsers.
--
-- The other parsing combinators require that the grammar being parsed
-- is LL(1). In some cases it may be difficult or even
-- impossible to transform a grammar into LL(1) form. As a remedy, we
-- include a non-deterministic version of the choice combinator in
-- addition to the deterministic combinator adapted from the paper. For
-- every symbol from the intersection of the parser's first sets, the
-- combinator '(<|?>)' applies both parsing functions to the input
-- stream and uses that one which processes the longer prefix of the
-- input stream irrespective of whether it succeeds or fails. If both
-- functions recognize the same prefix, we choose the one that succeeds
-- and report an ambiguous parse error if both succeed.
(<|?>) :: Symbol s => Parser a s b -> Parser a s b -> Parser a s b
Parser e1 ps1 <|?> Parser e2 ps2
  | isJust e1 && isJust e2 = failure "Ambiguous parser for empty word"
  | otherwise              = Parser (e1 `mplus` e2) (Map.union ps1' ps2)
  where
  ps1' = Map.fromList [ (s, maybe p (try p) (Map.lookup s ps2))
                      | (s, p) <- Map.toList ps1
                      ]
  try p1 p2 lexer success failp pos s =
    closeP1 p2s `thenP` \p2s' ->
    closeP1 p2f `thenP` \p2f' ->
    parse' p1 (retry p2s') (retry p2f')
    where p2s r1 = parse' p2       (select True   r1) (select False r1)
          p2f r1 = parse' p2 (flip (select False) r1) (select False r1)
          parse' p psucc pfail =
            p lexer (successK psucc) (failK pfail) pos s
          successK k x pos' s' = k (pos', success x pos' s')
          failK k pos' msg = k (pos', failp pos' msg)
          retry k (pos',p) = closeP0 p `thenP` curry k pos'
  select suc (pos1, p1) (pos2, p2) = case pos1 `compare` pos2 of
    GT -> p1
    EQ | suc       -> failP pos1 $ "Ambiguous parse before " ++ showPosition (span2Pos pos1)
       | otherwise -> p1
    LT -> p2

seqEE :: ParseFun a s (b -> c) -> ParseFun a s b -> ParseFun a s c
seqEE p1 p2 success failp = p1 (\f -> p2 (success . f) failp) failp

seqEP :: ParseFun a s (b -> c) -> (Lexer s a -> ParseFun a s b)
      -> Lexer s a -> ParseFun a s c
seqEP p1 p2 lexer success failp = p1 (\f -> p2 lexer (success . f) failp) failp

seqPP :: Symbol s => (Lexer s a -> ParseFun a s (b -> c)) -> Parser a s b
      -> Lexer s a -> ParseFun a s c
seqPP p1 p2 lexer success failp =
  p1 lexer (\f -> choose p2 lexer (success . f) failp) failp

-- ---------------------------------------------------------------------------
-- The combinators \verb|<\\>| and \verb|<\>| can be used to restrict
-- the first set of a parser. This is useful for combining two parsers
-- with an overlapping first set with the deterministic combinator <|>.
-- ---------------------------------------------------------------------------

-- |Restrict the first parser by the first 'Symbol's of the second
(<\>) :: Symbol s => Parser a s b -> Parser a s c -> Parser a s b
p <\> Parser _ ps = p <\\> Map.keys ps

-- |Restrict a parser by a list of first 'Symbol's
(<\\>) :: Symbol s => Parser a s b -> [s] -> Parser a s b
Parser e ps <\\> xs = Parser e (foldr Map.delete ps xs)

-- ---------------------------------------------------------------------------
-- Other combinators
-- Note that some of these combinators have not been published in the
-- paper, but were taken from the implementation found on the web.
-- ---------------------------------------------------------------------------

-- |Replace the result of the parser with the first argument
(<$->) :: Symbol s => a -> Parser b s c -> Parser b s a
f <$-> p = f <$ p

-- |Apply two parsers in sequence, but return only the result of the first
-- parser
(<*->) :: Symbol s => Parser a s b -> Parser a s c -> Parser a s b
p <*-> q = const <$> p <*> q

-- |Apply two parsers in sequence, but return only the result of the second
-- parser
(<-*>) :: Symbol s => Parser a s b -> Parser a s c -> Parser a s c
p <-*> q = id <$ p <*> q

-- |Apply the parsers in sequence and apply the result function of the second
-- parse to the result of the first
(<**>) :: Symbol s => Parser a s b -> Parser a s (b -> c) -> Parser a s c
p <**> q = flip ($) <$> p <*> q

-- |Same as (<**>), but only applies the function if the second parser
-- succeeded.
(<??>) :: Symbol s => Parser a s b -> Parser a s (b -> b) -> Parser a s b
p <??> q = p <**> (q `opt` id)

-- |Flipped function composition on parsers
(<.>) :: Symbol s => Parser a s (b -> c) -> Parser a s (c -> d)
      -> Parser a s (b -> d)
p1 <.> p2 = p1 <**> ((.) <$> p2)

-- |Try the first parser, but return the second argument if it didn't succeed
opt :: Symbol s => Parser a s b -> b -> Parser a s b
p `opt` x = p <|> succeed x

-- |Choose the first succeeding parser from a non-empty list of parsers
choice :: Symbol s => [Parser a s b] -> Parser a s b
choice = foldr1 (<|>)

-- |Try to apply a given parser and return a boolean value if the parser
-- succeeded.
flag :: Symbol s => Parser a s b -> Parser a s Bool
flag p = True <$-> p `opt` False

-- |Try to apply a parser but forget if it succeeded
optional :: Symbol s => Parser a s b -> Parser a s ()
optional p = void p `opt` ()

-- |Try to apply a parser and return its result in a 'Maybe' type
option :: Symbol s => Parser a s b -> Parser a s (Maybe b)
option p = Just <$> p `opt` Nothing

-- |Repeatedly apply a parser for 0 or more occurences
many :: Symbol s => Parser a s b -> Parser a s [b]
many p = many1 p `opt` []

-- |Repeatedly apply a parser for 1 or more occurences
many1 :: Symbol s => Parser a s b -> Parser a s [b]
many1 p = (:) <$> p <*> many p

-- |Parse a list with is separated by a seperator
sepBy :: Symbol s => Parser a s b -> Parser a s c -> Parser a s [b]
p `sepBy` q = p `sepBy1` q `opt` []

-- |Parse a non-empty list with is separated by a seperator
sepBy1 :: Symbol s => Parser a s b -> Parser a s c -> Parser a s [b]
p `sepBy1` q = (:) <$> p <*> many (q <-*> p)

-- |Parse a list with is separated by a seperator
sepBySp :: Symbol s => Parser a s b -> Parser a s c -> Parser a s ([b], [Span])
p `sepBySp` q = p `sepBy1Sp` q `opt` ([], [])

sepBy1Sp :: Symbol s => Parser a s b -> Parser a s c -> Parser a s ([b], [Span])
p `sepBy1Sp` q = comb <$> p <*> many ((,) <$> spanPosition <*-> q <*> p)
  where comb x xs = let (ss, ys) = unzip xs
                    in (x:ys,ss)

-- |@chainr p op x@ parses zero or more occurrences of @p@, separated by @op@.
-- Returns a value produced by a *right* associative application of all
-- functions returned by op. If there are no occurrences of @p@, @x@ is
-- returned.
chainr :: Symbol s
       => Parser a s b -> Parser a s (b -> b -> b) -> b -> Parser a s b
chainr p op x = chainr1 p op `opt` x

-- |Like 'chainr', but parses one or more occurrences of p.
chainr1 :: Symbol s => Parser a s b -> Parser a s (b -> b -> b) -> Parser a s b
chainr1 p op = r where r = p <**> (flip <$> op <*> r `opt` id)

-- |@chainr p op x@ parses zero or more occurrences of @p@, separated by @op@.
-- Returns a value produced by a *left* associative application of all
-- functions returned by op. If there are no occurrences of @p@, @x@ is
-- returned.
chainl :: Symbol s
       => Parser a s b -> Parser a s (b -> b -> b) -> b -> Parser a s b
chainl p op x = chainl1 p op `opt` x

-- |Like 'chainl', but parses one or more occurrences of p.
chainl1 :: Symbol s => Parser a s b -> Parser a s (b -> b -> b) -> Parser a s b
chainl1 p op = foldF <$> p <*> many (flip <$> op <*> p)
  where foldF x []     = x
        foldF x (f:fs) = foldF (f x) fs

-- |Parse an expression between an opening and a closing part.
between :: Symbol s => Parser a s b -> Parser a s c -> Parser a s b
        -> Parser a s c
between open p close = open <-*> p <*-> close

-- |Parse one of the given operators
ops :: Symbol s => [(s, b)] -> Parser a s b
ops []              = failure "Curry.Base.LLParseComb.ops: empty list"
ops [(s, x)]        = x <$-> symbol s
ops ((s, x) : rest) = x <$-> symbol s <|> ops rest

-- ---------------------------------------------------------------------------
-- Layout combinators
-- Note that the layout functions grab the next token (and its position).
-- After modifying the layout context, the continuation is called with
-- the same token and an undefined result.
-- ---------------------------------------------------------------------------

-- |Disable layout-awareness for the following
layoutOff :: Symbol s => Parser a s b
layoutOff = Parser (Just off) Map.empty
  where off success _ pos = pushContext (-1) . success undefined pos

-- |Add a new scope for layout
layoutOn :: Symbol s => Parser a s b
layoutOn = Parser (Just on) Map.empty
  where on success _ pos = pushContext (column (span2Pos pos)) . success undefined pos

-- |End the current layout scope (or re-enable layout-awareness if it is
-- currently disabled
layoutEnd :: Symbol s => Parser a s b
layoutEnd = Parser (Just end) Map.empty
  where end success _ pos = popContext . success undefined pos
