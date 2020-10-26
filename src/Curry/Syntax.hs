{- |
    Module      :  $Header$
    Description :  Interface for reading and manipulating Curry source code
    Copyright   :  (c) 2009        Holger Siegel
                       2011 - 2013 Björn Peemöller
                       2016        Finn Teegen
                       2016        Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable
-}
module Curry.Syntax
  ( module Curry.Syntax.Type
  , module Curry.Syntax.Utils
  , L.Token (..), L.Category (..), L.Attributes (..)
  , unlit, unlitLexSource, unlitParseHeader, unlitParsePragmas, unlitParseModule
  , lexSource, parseInterface, parseHeader, parsePragmas, parseModule, parseGoal
  , pPrint, pPrintPrec
  , showModule
  ) where

import           Curry.Base.Monad             (CYM)
import           Curry.Base.Span              (Span)
import           Curry.Base.Pretty            (pPrint, pPrintPrec)
import qualified Curry.Files.Unlit       as U (unlit)

import qualified Curry.Syntax.Lexer      as L
import qualified Curry.Syntax.Parser     as P
import           Curry.Syntax.Pretty          ()
import           Curry.Syntax.ShowModule      (showModule)
import           Curry.Syntax.Type
import           Curry.Syntax.Utils

-- |Unliterate a LiterateCurry file, identity on normal Curry file.
unlit :: FilePath -> String -> CYM String
unlit = U.unlit

-- |Unliterate and return the result of a lexical analysis of the source
-- program @src@.
-- The result is a list of tuples consisting of a 'Span' and a 'Token'.
unlitLexSource :: FilePath -> String -> CYM [(Span, L.Token)]
unlitLexSource fn src = U.unlit fn src >>= L.lexSource fn

-- |Unliterate and parse only pragmas of a Curry 'Module'
unlitParsePragmas :: FilePath -> String -> CYM (Module ())
unlitParsePragmas fn src = U.unlit fn src >>= P.parsePragmas fn

-- |Unliterate and parse a Curry 'Module' header
unlitParseHeader :: FilePath -> String -> CYM (Module ())
unlitParseHeader fn src = U.unlit fn src >>= P.parseHeader fn

-- |Unliterate and parse a Curry 'Module'
unlitParseModule :: FilePath -> String -> CYM (Module ())
unlitParseModule fn src = U.unlit fn src >>= P.parseSource fn

-- |Return the result of a lexical analysis of the source program @src@.
-- The result is a list of tuples consisting of a 'Span' and a 'Token'.
lexSource :: FilePath -> String -> CYM [(Span, L.Token)]
lexSource = L.lexSource

-- |Parse a Curry 'Interface'
parseInterface :: FilePath -> String -> CYM Interface
parseInterface = P.parseInterface

-- |Parse only pragmas of a Curry 'Module'
parsePragmas :: FilePath -> String -> CYM (Module ())
parsePragmas = P.parsePragmas

-- |Parse a Curry 'Module' header
parseHeader :: FilePath -> String -> CYM (Module ())
parseHeader = P.parseHeader

-- |Parse a Curry 'Module'
parseModule :: FilePath -> String -> CYM (Module ())
parseModule = P.parseSource

-- |Parse a 'Goal', i.e. an expression with (optional) local declarations
parseGoal :: String -> CYM (Goal ())
parseGoal = P.parseGoal
