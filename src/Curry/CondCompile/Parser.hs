{- |
    Module      :  $Header$
    Description :  Parser for conditional compiling
    Copyright   :  (c) 2017-2024   Kai-Oliver Prott
                       2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides parsing capabilities for conditional compilation statements,
    supporting directives such as `#if`, `#ifdef`, `#ifndef`, `#define`, and `#undef`.
-}
module Curry.CondCompile.Parser where

import Data.Functor (($>))
import Text.Parsec

import Curry.CondCompile.Type

type Parser a = Parsec String () a

program :: Parser Program
program = statement `sepBy` eol <* eof

statement :: Parser Stmt
statement =  ifElse "if" condition If
         <|> ifElse "ifdef" identifier IfDef
         <|> ifElse "ifndef" identifier IfNDef
         <|> define
         <|> undef
         <|> line

ifElse :: String -> Parser a -> (a -> [Stmt] -> [Elif] -> Else -> Stmt)
       -> Parser Stmt
ifElse k p c = c <$> (try (many sp *> keyword k *> many1 sp) *> p <* many sp <* eol)
                 <*> many (statement <* eol)
                 <*> many (Elif <$> ((,) <$> (try (many sp *> keyword "elif" *> many1 sp) *> condition <* many sp <* eol)
                                         <*> many (statement <* eol)))
                 <*> (Else <$> optionMaybe
                                 (try (many sp *> keyword "else" *> many sp) *> eol *> many (statement <* eol)))
                 <*  try (many sp <* keyword "endif" <* many sp)

define :: Parser Stmt
define = Define <$> (try (many sp *> keyword "define" *> many1 sp) *> identifier <* many1 sp)
                <*> value <* many sp

undef :: Parser Stmt
undef = Undef <$> (try (many sp *> keyword "undef" *> many1 sp) *> identifier <* many sp)

line :: Parser Stmt
line = do
  sps <- many sp
  try $  ((char '#' <?> "") *> fail "unknown directive")
     <|> (Line . (sps ++) <$> manyTill anyChar (try (lookAhead (eol <|> eof))))

keyword :: String -> Parser String
keyword = string . ('#' :)

condition :: Parser Cond
condition =  (Defined  <$> (try (string  "defined(") *> many sp *> identifier <* many sp <* char ')'))
         <|> (NDefined <$> (try (string "!defined(") *> many sp *> identifier <* many sp <* char ')'))
         <|> (Comp <$> (identifier <* many sp) <*> operator <*> (many sp *> value) <?> "condition")

identifier :: Parser String
identifier = (:) <$> firstChar <*> many (firstChar <|> digit) <?> "identifier"
  where firstChar = letter <|> char '_'

operator :: Parser Op
operator = choice [ Leq <$ try (string "<=")
                  , Lt  <$ try (string "<")
                  , Geq <$ try (string ">=")
                  , Gt  <$ try (string ">")
                  , Neq <$ try (string "!=")
                  , Eq  <$ string "=="
                  ] <?> "operator"

value :: Parser Int
value = fmap read (many1 digit)

eol :: Parser ()
eol = endOfLine $> ()

sp :: Parser Char
sp = try $  lookAhead (eol *> unexpected "end of line" <?> "")
        <|> space
