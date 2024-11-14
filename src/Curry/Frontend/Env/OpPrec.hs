{- |
    Module      :  $Header$
    Description :  Environment of operator precedences
    Copyright   :  (c) 2002 - 2004, Wolfgang Lux
                       2011 - 2013, Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    In order to parse infix expressions correctly, the compiler must know
    the precedence and fixity of each operator. Operator precedences are
    associated with entities and will be checked after renaming was
    applied. Nevertheless, we need to save precedences for ambiguous names
    in order to handle them correctly while computing the exported
    interface of a module.

    If no fixity is assigned to an operator, it will be given the default
    precedence 9 and assumed to be a left-associative operator.

    /Note:/ this modified version uses Haskell type 'Integer'
    for representing the precedence. This change had to be done due to the
    introduction of unlimited integer constants in the parser / lexer.
-}
module Env.OpPrec
  ( OpPrec (..), defaultP, defaultAssoc, defaultPrecedence, mkPrec
  , OpPrecEnv,  PrecInfo (..), bindP, lookupP, qualLookupP, initOpPrecEnv
  ) where

import Curry.Base.Ident
import Curry.Base.Pretty (Pretty(..))
import Curry.Syntax      (Infix (..))

import Base.TopEnv

import Data.Maybe        (fromMaybe)

import Text.PrettyPrint

-- |Operator precedence.
data OpPrec = OpPrec Infix Precedence deriving Eq

type Precedence = Integer

-- TODO: Change to real show instance and provide Pretty instance
-- if used anywhere.
instance Show OpPrec where
  showsPrec _ (OpPrec fix p) = showString (assoc fix) . shows p
    where
    assoc InfixL = "left "
    assoc InfixR = "right "
    assoc Infix  = "non-assoc "

instance Pretty OpPrec where
  pPrint (OpPrec fix p) = pPrint fix <+> integer p

-- |Default operator declaration (associativity and precedence).
defaultP :: OpPrec
defaultP = OpPrec defaultAssoc defaultPrecedence

-- |Default operator associativity.
defaultAssoc :: Infix
defaultAssoc = InfixL

-- |Default operator precedence.
defaultPrecedence :: Precedence
defaultPrecedence = 9

mkPrec :: Maybe Precedence -> Precedence
mkPrec mprec = fromMaybe defaultPrecedence mprec

-- |Precedence information for an identifier.
data PrecInfo = PrecInfo QualIdent OpPrec deriving (Eq, Show)

instance Entity PrecInfo where
  origName (PrecInfo op _) = op

instance Pretty PrecInfo where
  pPrint (PrecInfo qid prec) = pPrint qid <+> pPrint prec

-- |Environment mapping identifiers to their operator precedence.
type OpPrecEnv = TopEnv PrecInfo

-- |Initial 'OpPrecEnv'.
initOpPrecEnv :: OpPrecEnv
initOpPrecEnv = predefTopEnv qConsId consPrec emptyTopEnv

-- |Precedence of list constructor.
consPrec :: PrecInfo
consPrec = PrecInfo qConsId (OpPrec InfixR 5)

-- |Bind an operator precedence.
bindP :: ModuleIdent -> Ident -> OpPrec -> OpPrecEnv -> OpPrecEnv
bindP m op p
  | hasGlobalScope op = bindTopEnv op info . qualBindTopEnv qop info
  | otherwise         = bindTopEnv op info
  where qop  = qualifyWith m op
        info = PrecInfo qop p

-- The lookup functions for the environment which maintains the operator
-- precedences are simpler than for the type and value environments
-- because they do not need to handle tuple constructors.

-- |Lookup the operator precedence for an 'Ident'.
lookupP :: Ident -> OpPrecEnv -> [PrecInfo]
lookupP = lookupTopEnv

-- |Lookup the operator precedence for an 'QualIdent'.
qualLookupP :: QualIdent -> OpPrecEnv -> [PrecInfo]
qualLookupP = qualLookupTopEnv
