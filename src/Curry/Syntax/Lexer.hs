{- |
    Module      :  $Header$
    Description :  A lexer for Curry
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2013 Björn Peemöller
                       2016        Finn Teegen
                       2016        Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable
-}
module Curry.Syntax.Lexer
  ( -- * Data types for tokens
    Token (..), Category (..), Attributes (..)

    -- * lexing functions
  , lexSource, lexer, fullLexer
  ) where

import Prelude hiding (fail)
import Data.Char
  ( chr, ord, isAlpha, isAlphaNum, isDigit, isHexDigit, isOctDigit
  , isSpace, isUpper, toLower
  )
import Data.List (intercalate)
import qualified Data.Map as Map
  (Map, union, lookup, findWithDefault, fromList)

import Curry.Base.LexComb
import Curry.Base.Position
import Curry.Base.Span

-- ---------------------------------------------------------------------------
-- Tokens. Note that the equality and ordering instances of Token disregard
-- the attributes, as so that the parser decides about accepting a token
-- just by its category.
-- ---------------------------------------------------------------------------

-- |Data type for curry lexer tokens
data Token = Token Category Attributes

instance Eq Token where
  Token c1 _ == Token c2 _ = c1 == c2

instance Ord Token where
  Token c1 _ `compare` Token c2 _ = c1 `compare` c2

instance Symbol Token where
  isEOF (Token c _) = c == EOF

  dist _ (Token VSemicolon         _) = (0,  0)
  dist _ (Token VRightBrace        _) = (0,  0)
  dist _ (Token EOF                _) = (0,  0)
  dist _ (Token DotDot             _) = (0,  1)
  dist _ (Token DoubleColon        _) = (0,  1)
  dist _ (Token LeftArrow          _) = (0,  1)
  dist _ (Token RightArrow         _) = (0,  1)
  dist _ (Token DoubleArrow        _) = (0,  1)
  dist _ (Token KW_do              _) = (0,  1)
  dist _ (Token KW_if              _) = (0,  1)
  dist _ (Token KW_in              _) = (0,  1)
  dist _ (Token KW_of              _) = (0,  1)
  dist _ (Token Id_as              _) = (0,  1)
  dist _ (Token KW_let             _) = (0,  2)
  dist _ (Token PragmaEnd          _) = (0,  2)
  dist _ (Token KW_case            _) = (0,  3)
  dist _ (Token KW_class           _) = (0,  4)
  dist _ (Token KW_data            _) = (0,  3)
  dist _ (Token KW_default         _) = (0,  6)
  dist _ (Token KW_deriving        _) = (0,  7)
  dist _ (Token KW_else            _) = (0,  3)
  dist _ (Token KW_free            _) = (0,  3)
  dist _ (Token KW_then            _) = (0,  3)
  dist _ (Token KW_type            _) = (0,  3)
  dist _ (Token KW_fcase           _) = (0,  4)
  dist _ (Token KW_infix           _) = (0,  4)
  dist _ (Token KW_instance        _) = (0,  7)
  dist _ (Token KW_where           _) = (0,  4)
  dist _ (Token Id_ccall           _) = (0,  4)
  dist _ (Token KW_import          _) = (0,  5)
  dist _ (Token KW_infixl          _) = (0,  5)
  dist _ (Token KW_infixr          _) = (0,  5)
  dist _ (Token KW_module          _) = (0,  5)
  dist _ (Token Id_forall          _) = (0,  5)
  dist _ (Token Id_hiding          _) = (0,  5)
  dist _ (Token KW_newtype         _) = (0,  6)
  dist _ (Token KW_external        _) = (0,  7)
  dist _ (Token Id_interface       _) = (0,  8)
  dist _ (Token Id_primitive       _) = (0,  8)
  dist _ (Token Id_qualified       _) = (0,  8)
  dist _ (Token Id_det             _) = (0,  2)
  dist _ (Token Id_D               _) = (0,  0)
  dist _ (Token Id_ND              _) = (0,  1)
  dist _ (Token PragmaHiding       _) = (0,  9)
  dist _ (Token PragmaLanguage     _) = (0, 11)
  dist _ (Token Id                 a) = distAttr False a
  dist _ (Token QId                a) = distAttr False a
  dist _ (Token Sym                a) = distAttr False a
  dist _ (Token QSym               a) = distAttr False a
  dist _ (Token IntTok             a) = distAttr False a
  dist _ (Token FloatTok           a) = distAttr False a
  dist _ (Token CharTok            a) = distAttr False a
  dist c (Token StringTok          a) = updColDist c (distAttr False a)
  dist _ (Token LineComment        a) = distAttr True  a
  dist c (Token NestedComment      a) = updColDist c (distAttr True  a)
  dist _ (Token PragmaOptions      a) = let (ld, cd) = distAttr False a
                                        in  (ld, cd + 11)
  dist _ _                            = (0, 0)

-- TODO: Comment
updColDist :: Int -> Distance -> Distance
updColDist c (ld, cd) = (ld, if ld == 0 then cd else cd - c + 1)

distAttr :: Bool -> Attributes -> Distance
distAttr isComment attr = case attr of
  NoAttributes              -> (0, 0)
  CharAttributes     _ orig -> (0, length orig + 1)
  IntAttributes      _ orig -> (0, length orig - 1)
  FloatAttributes    _ orig -> (0, length orig - 1)
  StringAttributes   _ orig
      -- comment without surrounding quotes
    | isComment             -> (ld, cd)
      -- string with one ending double quote or two surrounding double quotes
      -- (column distance + 1 / + 2)
    | '\n' `elem` orig      -> (ld, cd + 1)
    | otherwise             -> (ld, cd + 2)
    where ld = length (filter    (== '\n') orig)
          cd = length (takeWhile (/= '\n') (reverse orig)) - 1
  IdentAttributes    mid i  -> (0, length (intercalate "." (mid ++ [i])) - 1)
  OptionsAttributes mt args -> case mt of
                                 Nothing -> (0, distArgs + 1)
                                 Just t  -> (0, length t + distArgs + 2)
    where distArgs = length args

-- |Category of curry tokens
data Category
  -- literals
  = CharTok
  | IntTok
  | FloatTok
  | StringTok

  -- identifiers
  | Id   -- identifier
  | QId  -- qualified identifier
  | Sym  -- symbol
  | QSym -- qualified symbol

  -- punctuation symbols
  | LeftParen     -- (
  | RightParen    -- )
  | Semicolon     -- ;
  | LeftBrace     -- {
  | RightBrace    -- }
  | LeftBracket   -- [
  | RightBracket  -- ]
  | Comma         -- ,
  | Underscore    -- _
  | Backquote     -- `

  -- layout
  | VSemicolon         -- virtual ;
  | VRightBrace        -- virtual }

  -- reserved keywords
  | KW_case
  | KW_class
  | KW_data
  | KW_default
  | KW_deriving
  | KW_do
  | KW_else
  | KW_external
  | KW_fcase
  | KW_free
  | KW_if
  | KW_import
  | KW_in
  | KW_infix
  | KW_infixl
  | KW_infixr
  | KW_instance
  | KW_let
  | KW_module
  | KW_newtype
  | KW_of
  | KW_then
  | KW_type
  | KW_where

  -- reserved operators
  | At           -- @
  | Colon        -- :
  | DotDot       -- ..
  | DoubleColon  -- ::
  | Equals       -- =
  | Backslash    -- \
  | Bar          -- |
  | LeftArrow    -- <-
  | RightArrow   -- ->
  | Tilde        -- ~
  | DoubleArrow  -- =>

  -- special identifiers
  | Id_as
  | Id_ccall
  | Id_forall
  | Id_hiding
  | Id_interface
  | Id_primitive
  | Id_qualified
  | Id_det
  | Id_D
  | Id_ND

  -- special operators
  | SymDot      -- .
  | SymMinus    -- -

  -- special symbols
  | SymStar -- kind star (*)

  -- pragmas
  | PragmaLanguage -- {-# LANGUAGE
  | PragmaOptions  -- {-# OPTIONS
  | PragmaHiding   -- {-# HIDING
  | PragmaMethod   -- {-# METHOD
  | PragmaModule   -- {-# MODULE
  | PragmaEnd      -- #-}


  -- comments (only for full lexer) inserted by men & bbr
  | LineComment
  | NestedComment

  -- end-of-file token
  | EOF
    deriving (Eq, Ord)

-- There are different kinds of attributes associated with the tokens.
-- Most attributes simply save the string corresponding to the token.
-- However, for qualified identifiers, we also record the list of module
-- qualifiers. The values corresponding to a literal token are properly
-- converted already. To simplify the creation and extraction of
-- attribute values, we make use of records.

-- |Attributes associated to a token
data Attributes
  = NoAttributes
  | CharAttributes    { cval     :: Char        , original :: String }
  | IntAttributes     { ival     :: Integer     , original :: String }
  | FloatAttributes   { fval     :: Double      , original :: String }
  | StringAttributes  { sval     :: String      , original :: String }
  | IdentAttributes   { modulVal :: [String]    , sval     :: String }
  | OptionsAttributes { toolVal  :: Maybe String, toolArgs :: String }

instance Show Attributes where
  showsPrec _ NoAttributes             = showChar '_'
  showsPrec _ (CharAttributes    cv _) = shows cv
  showsPrec _ (IntAttributes     iv _) = shows iv
  showsPrec _ (FloatAttributes   fv _) = shows fv
  showsPrec _ (StringAttributes  sv _) = shows sv
  showsPrec _ (IdentAttributes  mid i) = showsEscaped
                                       $ intercalate "." $ mid ++ [i]
  showsPrec _ (OptionsAttributes mt s) = showsTool mt
                                       . showChar ' ' . showString s
    where showsTool = maybe id (\t -> showChar '_' . showString t)


-- ---------------------------------------------------------------------------
-- The 'Show' instance of 'Token' is designed to display all tokens in their
-- source representation.
-- ---------------------------------------------------------------------------

showsEscaped :: String -> ShowS
showsEscaped s = showChar '`' . showString s . showChar '\''

showsIdent :: Attributes -> ShowS
showsIdent a = showString "identifier " . shows a

showsSpecialIdent :: String -> ShowS
showsSpecialIdent s = showString "identifier " . showsEscaped s

showsOperator :: Attributes -> ShowS
showsOperator a = showString "operator " . shows a

showsSpecialOperator :: String -> ShowS
showsSpecialOperator s = showString "operator " . showsEscaped s

instance Show Token where
  showsPrec _ (Token Id                 a) = showsIdent a
  showsPrec _ (Token QId                a) = showString "qualified "
                                           . showsIdent a
  showsPrec _ (Token Sym                a) = showsOperator a
  showsPrec _ (Token QSym               a) = showString "qualified "
                                           . showsOperator a
  showsPrec _ (Token IntTok             a) = showString "integer "   . shows a
  showsPrec _ (Token FloatTok           a) = showString "float "     . shows a
  showsPrec _ (Token CharTok            a) = showString "character " . shows a
  showsPrec _ (Token StringTok          a) = showString "string "    . shows a
  showsPrec _ (Token LeftParen          _) = showsEscaped "("
  showsPrec _ (Token RightParen         _) = showsEscaped ")"
  showsPrec _ (Token Semicolon          _) = showsEscaped ";"
  showsPrec _ (Token LeftBrace          _) = showsEscaped "{"
  showsPrec _ (Token RightBrace         _) = showsEscaped "}"
  showsPrec _ (Token LeftBracket        _) = showsEscaped "["
  showsPrec _ (Token RightBracket       _) = showsEscaped "]"
  showsPrec _ (Token Comma              _) = showsEscaped ","
  showsPrec _ (Token Underscore         _) = showsEscaped "_"
  showsPrec _ (Token Backquote          _) = showsEscaped "`"
  showsPrec _ (Token VSemicolon         _)
    = showsEscaped ";" . showString " (inserted due to layout)"
  showsPrec _ (Token VRightBrace        _)
    = showsEscaped "}" . showString " (inserted due to layout)"
  showsPrec _ (Token At                 _) = showsEscaped "@"
  showsPrec _ (Token Colon              _) = showsEscaped ":"
  showsPrec _ (Token DotDot             _) = showsEscaped ".."
  showsPrec _ (Token DoubleArrow        _) = showsEscaped "=>"
  showsPrec _ (Token DoubleColon        _) = showsEscaped "::"
  showsPrec _ (Token Equals             _) = showsEscaped "="
  showsPrec _ (Token Backslash          _) = showsEscaped "\\"
  showsPrec _ (Token Bar                _) = showsEscaped "|"
  showsPrec _ (Token LeftArrow          _) = showsEscaped "<-"
  showsPrec _ (Token RightArrow         _) = showsEscaped "->"
  showsPrec _ (Token Tilde              _) = showsEscaped "~"
  showsPrec _ (Token SymDot             _) = showsSpecialOperator "."
  showsPrec _ (Token SymMinus           _) = showsSpecialOperator "-"
  showsPrec _ (Token SymStar            _) = showsEscaped "*"
  showsPrec _ (Token KW_case            _) = showsEscaped "case"
  showsPrec _ (Token KW_class           _) = showsEscaped "class"
  showsPrec _ (Token KW_data            _) = showsEscaped "data"
  showsPrec _ (Token KW_default         _) = showsEscaped "default"
  showsPrec _ (Token KW_deriving        _) = showsEscaped "deriving"
  showsPrec _ (Token KW_do              _) = showsEscaped "do"
  showsPrec _ (Token KW_else            _) = showsEscaped "else"
  showsPrec _ (Token KW_external        _) = showsEscaped "external"
  showsPrec _ (Token KW_fcase           _) = showsEscaped "fcase"
  showsPrec _ (Token KW_free            _) = showsEscaped "free"
  showsPrec _ (Token KW_if              _) = showsEscaped "if"
  showsPrec _ (Token KW_import          _) = showsEscaped "import"
  showsPrec _ (Token KW_in              _) = showsEscaped "in"
  showsPrec _ (Token KW_infix           _) = showsEscaped "infix"
  showsPrec _ (Token KW_infixl          _) = showsEscaped "infixl"
  showsPrec _ (Token KW_infixr          _) = showsEscaped "infixr"
  showsPrec _ (Token KW_instance        _) = showsEscaped "instance"
  showsPrec _ (Token KW_let             _) = showsEscaped "let"
  showsPrec _ (Token KW_module          _) = showsEscaped "module"
  showsPrec _ (Token KW_newtype         _) = showsEscaped "newtype"
  showsPrec _ (Token KW_of              _) = showsEscaped "of"
  showsPrec _ (Token KW_then            _) = showsEscaped "then"
  showsPrec _ (Token KW_type            _) = showsEscaped "type"
  showsPrec _ (Token KW_where           _) = showsEscaped "where"
  showsPrec _ (Token Id_as              _) = showsSpecialIdent "as"
  showsPrec _ (Token Id_ccall           _) = showsSpecialIdent "ccall"
  showsPrec _ (Token Id_forall          _) = showsSpecialIdent "forall"
  showsPrec _ (Token Id_hiding          _) = showsSpecialIdent "hiding"
  showsPrec _ (Token Id_interface       _) = showsSpecialIdent "interface"
  showsPrec _ (Token Id_primitive       _) = showsSpecialIdent "primitive"
  showsPrec _ (Token Id_qualified       _) = showsSpecialIdent "qualified"
  showsPrec _ (Token Id_det             _) = showsSpecialIdent "det"
  showsPrec _ (Token Id_D               _) = showsSpecialIdent "D"
  showsPrec _ (Token Id_ND              _) = showsSpecialIdent "ND"
  showsPrec _ (Token PragmaLanguage     _) = showString "{-# LANGUAGE"
  showsPrec _ (Token PragmaOptions      a) = showString "{-# OPTIONS"
                                           . shows a
  showsPrec _ (Token PragmaHiding       _) = showString "{-# HIDING"
  showsPrec _ (Token PragmaMethod       _) = showString "{-# METHOD"
  showsPrec _ (Token PragmaModule       _) = showString "{-# MODULE"
  showsPrec _ (Token PragmaEnd          _) = showString "#-}"
  showsPrec _ (Token LineComment        a) = shows a
  showsPrec _ (Token NestedComment      a) = shows a
  showsPrec _ (Token EOF                _) = showString "<end-of-file>"

-- ---------------------------------------------------------------------------
-- The following functions can be used to construct tokens with
-- specific attributes.
-- ---------------------------------------------------------------------------

-- |Construct a simple 'Token' without 'Attributes'
tok :: Category -> Token
tok t = Token t NoAttributes

-- |Construct a 'Token' for a single 'Char'
charTok :: Char -> String -> Token
charTok c o = Token CharTok CharAttributes { cval = c, original = o }

-- |Construct a 'Token' for an int value
intTok :: Integer -> String -> Token
intTok base digits = Token IntTok IntAttributes
  { ival = convertIntegral base digits, original = digits }

-- |Construct a 'Token' for a float value
floatTok :: String -> String -> Int -> String -> Token
floatTok mant frac expo rest = Token FloatTok FloatAttributes
  { fval     = convertFloating mant frac expo
  , original = mant ++ "." ++ frac ++ rest }

-- |Construct a 'Token' for a string value
stringTok :: String -> String -> Token
stringTok cs s = Token StringTok StringAttributes { sval = cs, original = s }

-- |Construct a 'Token' for identifiers
idTok :: Category -> [String] -> String -> Token
idTok t mIdent ident = Token t
  IdentAttributes { modulVal = mIdent, sval = ident }

-- TODO
pragmaOptionsTok :: Maybe String -> String -> Token
pragmaOptionsTok mbTool s = Token PragmaOptions
  OptionsAttributes { toolVal = mbTool, toolArgs = s }

-- |Construct a 'Token' for a line comment
lineCommentTok :: String -> Token
lineCommentTok s = Token LineComment
  StringAttributes { sval = s, original = s }

-- |Construct a 'Token' for a nested comment
nestedCommentTok :: String -> Token
nestedCommentTok s = Token NestedComment
  StringAttributes { sval = s, original = s }

-- ---------------------------------------------------------------------------
-- Tables for reserved operators and identifiers
-- ---------------------------------------------------------------------------

-- |Map of reserved operators
reservedOps:: Map.Map String Category
reservedOps = Map.fromList
  [ ("@" , At         )
  , (":" , Colon      )
  , ("=>", DoubleArrow)
  , ("::", DoubleColon)
  , ("..", DotDot     )
  , ("=" , Equals     )
  , ("\\", Backslash  )
  , ("|" , Bar        )
  , ("<-", LeftArrow  )
  , ("->", RightArrow )
  , ("~" , Tilde      )
  ]

-- |Map of reserved and special operators
reservedSpecialOps :: Map.Map String Category
reservedSpecialOps = Map.union reservedOps $ Map.fromList
  [ ("." , SymDot     )
  , ("-" , SymMinus   )
  , ("*" , SymStar    )
  ]

-- |Map of keywords
keywords :: Map.Map String Category
keywords = Map.fromList
  [ ("case"    , KW_case    )
  , ("class"   , KW_class   )
  , ("data"    , KW_data    )
  , ("default" , KW_default )
  , ("deriving", KW_deriving)
  , ("do"      , KW_do      )
  , ("else"    , KW_else    )
  , ("external", KW_external)
  , ("fcase"   , KW_fcase   )
  , ("free"    , KW_free    )
  , ("if"      , KW_if      )
  , ("import"  , KW_import  )
  , ("in"      , KW_in      )
  , ("infix"   , KW_infix   )
  , ("infixl"  , KW_infixl  )
  , ("infixr"  , KW_infixr  )
  , ("instance", KW_instance)
  , ("let"     , KW_let     )
  , ("module"  , KW_module  )
  , ("newtype" , KW_newtype )
  , ("of"      , KW_of      )
  , ("then"    , KW_then    )
  , ("type"    , KW_type    )
  , ("where"   , KW_where   )
  ]

-- |Map of keywords and special identifiers
keywordsSpecialIds :: Map.Map String Category
keywordsSpecialIds = Map.union keywords $ Map.fromList
  [ ("as"       , Id_as       )
  , ("ccall"    , Id_ccall    )
  , ("forall"   , Id_forall   )
  , ("hiding"   , Id_hiding   )
  , ("interface", Id_interface)
  , ("primitive", Id_primitive)
  , ("qualified", Id_qualified)
  ]

pragmas :: Map.Map String Category
pragmas = Map.fromList
  [ ("language", PragmaLanguage)
  , ("options" , PragmaOptions )
  , ("hiding"  , PragmaHiding  )
  , ("method"  , PragmaMethod  )
  , ("module"  , PragmaModule  )
  ]


-- ---------------------------------------------------------------------------
-- Character classes
-- ---------------------------------------------------------------------------

-- |Check whether a 'Char' is allowed for identifiers
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c `elem` "'_"

-- |Check whether a 'Char' is allowed for symbols
isSymbolChar :: Char -> Bool
isSymbolChar c = c `elem` "~!@#$%^&*+-=<>:?./|\\"

-- ---------------------------------------------------------------------------
-- Lexing functions
-- ---------------------------------------------------------------------------

-- |Lex source code
lexSource :: FilePath -> String -> CYM [(Span, Token)]
lexSource = parse (applyLexer fullLexer)

-- |CPS-Lexer for Curry
lexer :: Lexer Token a
lexer = skipWhiteSpace True -- skip comments

-- |CPS-Lexer for Curry which also lexes comments.
-- This lexer is useful for documentation tools.
fullLexer :: Lexer Token a
fullLexer = skipWhiteSpace False -- lex comments

-- |Lex the source code and skip whitespaces
skipWhiteSpace :: Bool -> Lexer Token a
skipWhiteSpace skipComments suc fail = skip
  where
  skip sp   []              bol = suc sp (tok EOF)                   sp            [] bol
  skip sp c@('-':'-':_)     _   = lexLineComment     sucComment fail sp            c  True
  skip sp c@('{':'-':'#':_) bol = lexPragma noPragma suc        fail sp            c  bol
  skip sp c@('{':'-':_)     bol = lexNestedComment   sucComment fail sp            c  bol
  skip sp cs@(c:s)          bol
    | c == '\t'                = warnP sp "Tab character" skip       (tabSpan  sp) s  bol
    | c == '\n'                = skip                                (nlSpan   sp) s  True
    | isSpace c                = skip                                (nextSpan sp) s  bol
    | bol                      = lexBOL             suc        fail  sp            cs bol
    | otherwise                = lexToken           suc        fail  sp            cs bol
  sucComment = if skipComments then (\ _suc _fail -> skip) else suc
  noPragma   = lexNestedComment sucComment fail

-- Lex a line comment
lexLineComment :: Lexer Token a
lexLineComment suc _ sp str = case break (== '\n') str of
  (c, s ) -> suc sp (lineCommentTok c) (incrSpan sp $ length c) s

lexPragma :: P a -> Lexer Token a
lexPragma noPragma suc fail sp0 str = pragma (incrSpan sp0 3) (drop 3 str)
  where
  skip = noPragma sp0 str
  pragma sp []         = fail sp0 "Unterminated pragma" sp []
  pragma sp cs@(c : s)
    | c == '\t' = pragma (tabSpan  sp) s
    | c == '\n' = pragma (nlSpan   sp) s
    | isSpace c = pragma (nextSpan sp) s
    | isAlpha c = case Map.lookup (map toLower prag) pragmas of
        Nothing            -> skip
        Just PragmaOptions -> lexOptionsPragma sp0 suc fail sp1 rest
        Just t             -> suc sp0 (tok t)               sp1 rest
    | otherwise = skip
    where
    (prag, rest) = span isAlphaNum cs
    sp1          = incrSpan sp (length prag)

lexOptionsPragma :: Span -> Lexer Token a
lexOptionsPragma sp0 _   fail sp [] = fail sp0 "Unterminated Options pragma" sp []
lexOptionsPragma sp0 suc fail sp (c : s)
  | c == '\t' = lexArgs Nothing (tabSpan  sp) s
  | c == '\n' = lexArgs Nothing (nlSpan   sp) s
  | isSpace c = lexArgs Nothing (nextSpan sp) s
  | c == '_'  = let (tool, s1) = span isIdentChar s
                in  lexArgs (Just tool) (incrSpan sp (length tool + 1)) s1
  | otherwise = fail sp0 "Malformed Options pragma" sp s
  where
  lexArgs mbTool = lexRaw ""
    where
    lexRaw s0 sp1 r = case hash of
      []            -> fail sp0 "End-of-file inside pragma" (incrSpan sp1 len) []
      '#':'-':'}':_ -> token  (trim $ s0 ++ opts) (incrSpan sp1 len)       hash
      _             -> lexRaw (s0 ++ opts ++ "#") (incrSpan sp1 (len + 1)) (drop 1 hash)
      where
      (opts, hash) = span (/= '#') r
      len = length opts
      token = suc sp0 . pragmaOptionsTok mbTool
      trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- Lex a nested comment
lexNestedComment :: Lexer Token a
lexNestedComment suc fail sp0 = lnc (0 :: Integer) id sp0
  where
  -- d   : nesting depth
  -- comm: comment already lexed as functional list
  lnc d comm sp str = case (d, str) of
    (_,        []) -> fail sp0    "Unterminated nested comment"  sp          []
    (1, '-':'}':s) -> suc  sp0    (nestedCommentTok (comm "-}")) (incrSpan sp 2) s
    (_, '{':'-':s) -> cont (d+1) ("{-" ++)                       (incrSpan sp 2) s
    (_, '-':'}':s) -> cont (d-1) ("-}" ++)                       (incrSpan sp 2) s
    (_, c@'\t' :s) -> cont d     (c:)                            (tabSpan    sp) s
    (_, c@'\n' :s) -> cont d     (c:)                            (nlSpan     sp) s
    (_, c      :s) -> cont d     (c:)                            (nextSpan   sp) s
    where cont d' comm' = lnc d' (comm . comm')

-- Lex tokens at the beginning of a line, managing layout.
lexBOL :: Lexer Token a
lexBOL suc fail sp s _ []            = lexToken suc fail sp s False []
lexBOL suc fail sp s _ ctxt@(n:rest)
  | col <  n  = suc sp (tok VRightBrace) sp s True  rest
  | col == n  = lexSemiOrWhere suc fail  sp s False ctxt
  | otherwise = lexToken       suc fail  sp s False ctxt
  where col = column (span2Pos sp)

lexSemiOrWhere :: Lexer Token a
lexSemiOrWhere suc _ sp ('w':'h':'e':'r':'e':s@(c:_))
  | not (isIdentChar c)   = suc sp (tok KW_where)   sp s
lexSemiOrWhere suc _ sp s = suc sp (tok VSemicolon) sp s

-- Lex a single 'Token'
lexToken :: Lexer Token a
lexToken suc _    sp []       = suc sp (tok EOF) sp []
lexToken suc fail sp cs@(c:s)
  | take 3 cs == "#-}" = suc sp (tok PragmaEnd) (incrSpan sp 3) (drop 3 cs)
  | c == '('           = token LeftParen
  | c == ')'           = token RightParen
  | c == ','           = token Comma
  | c == ';'           = token Semicolon
  | c == '['           = token LeftBracket
  | c == ']'           = token RightBracket
  | c == '_'           = token Underscore
  | c == '`'           = token Backquote
  | c == '{'           = token LeftBrace
  | c == '}'           = lexRightBrace (suc sp) (nextSpan sp) s
  | c == '\''          = lexChar   sp suc fail  (nextSpan sp) s
  | c == '\"'          = lexString sp suc fail  (nextSpan sp) s
  | isAlpha      c     = lexIdent      (suc sp) sp            cs
  | isSymbolChar c     = lexSymbol     (suc sp) sp            cs
  | isDigit      c     = lexNumber     (suc sp) sp            cs
  | otherwise          = fail sp ("Illegal character " ++ show c) sp s
  where token t = suc sp (tok t) (nextSpan sp) s

-- Lex a right brace and pop from the context stack
lexRightBrace :: (Token -> P a) -> P a
lexRightBrace cont sp s bol ctxt = cont (tok RightBrace) sp s bol (drop 1 ctxt)

-- Lex an identifier
lexIdent :: (Token -> P a) -> P a
lexIdent cont sp s = maybe (lexOptQual cont (token Id) [ident]) (cont . token)
                          (Map.lookup ident keywordsSpecialIds)
                          (incrSpan sp $ length ident) rest
  where (ident, rest) = span isIdentChar s
        token t       = idTok t [] ident

-- Lex a symbol
lexSymbol :: (Token -> P a) -> P a
lexSymbol cont sp s = cont
  (idTok (Map.findWithDefault Sym sym reservedSpecialOps) [] sym)
  (incrSpan sp $ length sym) rest
  where (sym, rest) = span isSymbolChar s

-- Lex an optionally qualified entity (identifier or symbol).
lexOptQual :: (Token -> P a) -> Token -> [String] -> P a
lexOptQual cont token mIdent sp cs@('.':c:s)
  | isAlpha  c                 = lexQualIdent cont identCont mIdent
                                   (nextSpan sp) (c:s)
  | isSymbolChar c && c /= '.' = lexQualSymbol cont identCont mIdent
                                   (nextSpan sp) (c:s)
--   | c `elem` ":[("   = lexQualPrimitive cont token     mIdent (nextSpan sp) (c:s)
  where identCont _ _ = cont token sp cs
lexOptQual cont token mIdent sp cs@('.':'.':c:s)
  |       isSymbolChar c =       lexQualSymbol cont identCont mIdent
                                   (nextSpan sp) ('.':c:s)
  | not $ isIdentChar  c =       lexQualSymbol cont identCont mIdent
                                   (nextSpan sp) ('.':c:s)
  where identCont _ _ = cont token sp cs
lexOptQual cont token _      sp cs = cont token sp cs

-- Lex a qualified identifier.
lexQualIdent :: (Token -> P a) -> P a -> [String] -> P a
lexQualIdent cont identCont mIdent sp s =
  maybe (lexOptQual cont (idTok QId mIdent ident) (mIdent ++ [ident]))
        (const identCont)
        (Map.lookup ident keywords)
        (incrSpan sp (length ident)) rest
  where (ident, rest) = span isIdentChar s

-- Lex a qualified symbol.
lexQualSymbol :: (Token -> P a) -> P a -> [String] -> P a
lexQualSymbol cont identCont mIdent sp s =
  maybe (cont (idTok QSym mIdent sym)) (const identCont)
        (Map.lookup sym reservedOps)
        (incrSpan sp (length sym)) rest
  where (sym, rest) = span isSymbolChar s

-- ---------------------------------------------------------------------------
-- /Note:/ since Curry allows an unlimited range of integer numbers,
-- read numbers must be converted to Haskell type 'Integer'.
-- ---------------------------------------------------------------------------

-- Lex a numeric literal.
lexNumber :: (Token -> P a) -> P a
lexNumber cont sp ('0':c:s)
  | c `elem` "bB"  = lexBinary      cont nullCont (incrSpan sp 2) s
  | c `elem` "oO"  = lexOctal       cont nullCont (incrSpan sp 2) s
  | c `elem` "xX"  = lexHexadecimal cont nullCont (incrSpan sp 2) s
  where nullCont _ _ = cont (intTok 10 "0") (nextSpan sp) (c:s)
lexNumber cont sp s = lexOptFraction cont (intTok 10 digits) digits
                     (incrSpan sp $ length digits) rest
  where (digits, rest) = span isDigit s

-- Lex a binary literal.
lexBinary :: (Token -> P a) -> P a -> P a
lexBinary cont nullCont sp s
  | null digits = nullCont undefined undefined
  | otherwise   = cont (intTok 2 digits) (incrSpan sp $ length digits) rest
  where (digits, rest) = span isBinDigit s
        isBinDigit c   = c >= '0' && c <= '1'

-- Lex an octal literal.
lexOctal :: (Token -> P a) -> P a -> P a
lexOctal cont nullCont sp s
  | null digits = nullCont undefined undefined
  | otherwise   = cont (intTok 8 digits) (incrSpan sp $ length digits) rest
  where (digits, rest) = span isOctDigit s

-- Lex a hexadecimal literal.
lexHexadecimal :: (Token -> P a) -> P a -> P a
lexHexadecimal cont nullCont sp s
  | null digits = nullCont undefined undefined
  | otherwise   = cont (intTok 16 digits) (incrSpan sp $ length digits) rest
  where (digits, rest) = span isHexDigit s

-- Lex an optional fractional part (float literal).
lexOptFraction :: (Token -> P a) -> Token -> String -> P a
lexOptFraction cont _ mant sp ('.':c:s)
  | isDigit c = lexOptExponent cont (floatTok mant frac 0 "") mant frac
                               (incrSpan sp (length frac+1)) rest
  where (frac,rest) = span isDigit (c:s)
lexOptFraction cont token mant sp (c:s)
  | c `elem` "eE" = lexSignedExponent cont intCont mant "" [c] (nextSpan sp) s
  where intCont _ _ = cont token sp (c:s)
lexOptFraction cont token _ sp s = cont token sp s

-- Lex an optional exponent (float literal).
lexOptExponent :: (Token -> P a) -> Token -> String -> String -> P a
lexOptExponent cont token mant frac sp (c:s)
  | c `elem` "eE" = lexSignedExponent cont floatCont mant frac [c] (nextSpan sp) s
  where floatCont _ _ = cont token sp (c:s)
lexOptExponent cont token _    _    sp s = cont token sp s

-- Lex an exponent with sign (float literal).
lexSignedExponent :: (Token -> P a) -> P a -> String -> String -> String
                  -> P a
lexSignedExponent cont floatCont mant frac e sp str = case str of
  ('+':c:s) | isDigit c -> lexExpo (e ++ "+") id     (nextSpan sp) (c:s)
  ('-':c:s) | isDigit c -> lexExpo (e ++ "-") negate (nextSpan sp) (c:s)
  (c:_)     | isDigit c -> lexExpo e          id     sp            str
  _                     -> floatCont                 sp            str
  where lexExpo = lexExponent cont mant frac

-- Lex an exponent without sign (float literal).
lexExponent :: (Token -> P a) -> String -> String -> String -> (Int -> Int)
            -> P a
lexExponent cont mant frac e expSign sp s =
  cont (floatTok mant frac expo (e ++ digits)) (incrSpan sp $ length digits) rest
  where (digits, rest) = span isDigit s
        expo           = expSign (convertIntegral 10 digits)

-- Lex a character literal.
lexChar :: Span -> Lexer Token a
lexChar sp0 _       fail sp []    = fail sp0 "Illegal character constant" sp []
lexChar sp0 success fail sp (c:s)
  | c == '\\' = lexEscape sp (\d o -> lexCharEnd d o sp0 success fail)
                          fail (nextSpan sp) s
  | c == '\n' = fail sp0 "Illegal character constant" sp (c:s)
  | c == '\t' = lexCharEnd c "\t" sp0 success fail (tabSpan  sp) s
  | otherwise = lexCharEnd c [c]  sp0 success fail (nextSpan sp) s

-- Lex the end of a character literal.
lexCharEnd :: Char -> String -> Span -> Lexer Token a
lexCharEnd c o sp0 suc _    sp ('\'':s) = suc sp0 (charTok c o) (nextSpan sp) s
lexCharEnd _ _ sp0 _   fail sp s        =
  fail sp0 "Improperly terminated character constant" sp s

-- Lex a String literal.
lexString :: Span -> Lexer Token a
lexString sp0 suc fail = lexStringRest "" id
  where
  lexStringRest _  _  sp []    = improperTermination sp
  lexStringRest s0 so sp (c:s)
    | c == '\n' = improperTermination sp
    | c == '\"' = suc sp0 (stringTok (reverse s0) (so "")) (nextSpan sp) s
    | c == '\\' = lexStringEscape sp s0 so lexStringRest fail (nextSpan sp) s
    | c == '\t' = lexStringRest (c:s0) (so . (c:)) (tabSpan  sp) s
    | otherwise = lexStringRest (c:s0) (so . (c:)) (nextSpan sp) s
  improperTermination sp = fail sp0 "Improperly terminated string constant" sp []

-- Lex an escaped character inside a string.
lexStringEscape ::  Span -> String -> (String -> String)
                -> (String -> (String -> String) -> P a)
                -> FailP a -> P a
lexStringEscape sp0 _  _  _   fail sp []      = lexEscape sp0 undefined fail sp []
lexStringEscape sp0 s0 so suc fail sp cs@(c:s)
    -- The escape sequence represents an empty character of length zero
  | c == '&'  = suc s0 (so . ("\\&" ++)) (nextSpan sp) s
  | isSpace c = lexStringGap so (suc s0) fail sp cs
  | otherwise = lexEscape sp0 (\ c' s' -> suc (c': s0) (so . (s' ++))) fail sp cs

-- Lex a string gap.
lexStringGap :: (String -> String) -> ((String -> String) -> P a)
             -> FailP a -> P a
lexStringGap _  _   fail sp []    = fail sp "End-of-file in string gap" sp []
lexStringGap so suc fail sp (c:s)
  | c == '\\' = suc          (so . (c:))          (nextSpan sp) s
  | c == '\t' = lexStringGap (so . (c:)) suc fail (tabSpan  sp) s
  | c == '\n' = lexStringGap (so . (c:)) suc fail (nlSpan   sp) s
  | isSpace c = lexStringGap (so . (c:)) suc fail (nextSpan sp) s
  | otherwise = fail sp ("Illegal character in string gap: " ++ show c) sp s

-- Lex an escaped character.
lexEscape :: Span -> (Char -> String -> P a) -> FailP a -> P a
lexEscape sp0 suc fail sp str = case str of
  -- character escape
  ('a' :s) -> suc '\a' "\\a"  (nextSpan sp) s
  ('b' :s) -> suc '\b' "\\b"  (nextSpan sp) s
  ('f' :s) -> suc '\f' "\\f"  (nextSpan sp) s
  ('n' :s) -> suc '\n' "\\n"  (nextSpan sp) s
  ('r' :s) -> suc '\r' "\\r"  (nextSpan sp) s
  ('t' :s) -> suc '\t' "\\t"  (nextSpan sp) s
  ('v' :s) -> suc '\v' "\\v"  (nextSpan sp) s
  ('\\':s) -> suc '\\' "\\\\" (nextSpan sp) s
  ('"' :s) -> suc '\"' "\\\"" (nextSpan sp) s
  ('\'':s) -> suc '\'' "\\\'" (nextSpan sp) s
  -- control characters
  ('^':c:s) | isControlEsc c -> controlEsc c (incrSpan sp 2) s
  -- numeric escape
  ('o':c:s) | isOctDigit c   -> numEsc  8 isOctDigit ("\\o" ++) (nextSpan sp) (c:s)
  ('x':c:s) | isHexDigit c   -> numEsc 16 isHexDigit ("\\x" ++) (nextSpan sp) (c:s)
  (c:s)     | isDigit    c   -> numEsc 10 isDigit    ("\\"  ++) sp            (c:s)
  -- ascii escape
  _        -> asciiEscape sp0 suc fail sp str
  where numEsc         = numEscape sp0 suc fail
        controlEsc   c = suc (chr (ord c `mod` 32)) ("\\^" ++ [c])
        isControlEsc c = isUpper c || c `elem` "@[\\]^_"

numEscape :: Span -> (Char -> String -> P a) -> FailP a -> Int
          -> (Char -> Bool) -> (String -> String) -> P a
numEscape sp0 suc fail b isDigit' so sp s
  | n >= ord minBound && n <= ord maxBound
   = suc (chr n) (so digits) (incrSpan sp $ length digits) rest
  | otherwise
  = fail sp0 "Numeric escape out-of-range" sp s
  where (digits, rest) = span isDigit' s
        n = convertIntegral b digits

asciiEscape :: Span -> (Char -> String -> P a) -> FailP a -> P a
asciiEscape sp0 suc fail sp str = case str of
  ('N':'U':'L':s) -> suc '\NUL' "\\NUL" (incrSpan sp 3) s
  ('S':'O':'H':s) -> suc '\SOH' "\\SOH" (incrSpan sp 3) s
  ('S':'T':'X':s) -> suc '\STX' "\\STX" (incrSpan sp 3) s
  ('E':'T':'X':s) -> suc '\ETX' "\\ETX" (incrSpan sp 3) s
  ('E':'O':'T':s) -> suc '\EOT' "\\EOT" (incrSpan sp 3) s
  ('E':'N':'Q':s) -> suc '\ENQ' "\\ENQ" (incrSpan sp 3) s
  ('A':'C':'K':s) -> suc '\ACK' "\\ACK" (incrSpan sp 3) s
  ('B':'E':'L':s) -> suc '\BEL' "\\BEL" (incrSpan sp 3) s
  ('B':'S'    :s) -> suc '\BS'  "\\BS"  (incrSpan sp 2) s
  ('H':'T'    :s) -> suc '\HT'  "\\HT"  (incrSpan sp 2) s
  ('L':'F'    :s) -> suc '\LF'  "\\LF"  (incrSpan sp 2) s
  ('V':'T'    :s) -> suc '\VT'  "\\VT"  (incrSpan sp 2) s
  ('F':'F'    :s) -> suc '\FF'  "\\FF"  (incrSpan sp 2) s
  ('C':'R'    :s) -> suc '\CR'  "\\CR"  (incrSpan sp 2) s
  ('S':'O'    :s) -> suc '\SO'  "\\SO"  (incrSpan sp 2) s
  ('S':'I'    :s) -> suc '\SI'  "\\SI"  (incrSpan sp 2) s
  ('D':'L':'E':s) -> suc '\DLE' "\\DLE" (incrSpan sp 3) s
  ('D':'C':'1':s) -> suc '\DC1' "\\DC1" (incrSpan sp 3) s
  ('D':'C':'2':s) -> suc '\DC2' "\\DC2" (incrSpan sp 3) s
  ('D':'C':'3':s) -> suc '\DC3' "\\DC3" (incrSpan sp 3) s
  ('D':'C':'4':s) -> suc '\DC4' "\\DC4" (incrSpan sp 3) s
  ('N':'A':'K':s) -> suc '\NAK' "\\NAK" (incrSpan sp 3) s
  ('S':'Y':'N':s) -> suc '\SYN' "\\SYN" (incrSpan sp 3) s
  ('E':'T':'B':s) -> suc '\ETB' "\\ETB" (incrSpan sp 3) s
  ('C':'A':'N':s) -> suc '\CAN' "\\CAN" (incrSpan sp 3) s
  ('E':'M'    :s) -> suc '\EM'  "\\EM"  (incrSpan sp 2) s
  ('S':'U':'B':s) -> suc '\SUB' "\\SUB" (incrSpan sp 3) s
  ('E':'S':'C':s) -> suc '\ESC' "\\ESC" (incrSpan sp 3) s
  ('F':'S'    :s) -> suc '\FS'  "\\FS"  (incrSpan sp 2) s
  ('G':'S'    :s) -> suc '\GS'  "\\GS"  (incrSpan sp 2) s
  ('R':'S'    :s) -> suc '\RS'  "\\RS"  (incrSpan sp 2) s
  ('U':'S'    :s) -> suc '\US'  "\\US"  (incrSpan sp 2) s
  ('S':'P'    :s) -> suc '\SP'  "\\SP"  (incrSpan sp 2) s
  ('D':'E':'L':s) -> suc '\DEL' "\\DEL" (incrSpan sp 3) s
  s               -> fail sp0 "Illegal escape sequence" sp s
