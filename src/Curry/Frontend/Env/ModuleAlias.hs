{- |
    Module      :  $Header$
    Description :  Environment of module aliases
    Copyright   :  (c) 2002 - 2004, Wolfgang Lux
                       2011 - 2013, Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides an environment for resolving module aliases.

    For example, if module @FiniteMap@ is imported via

    @import FiniteMap as FM@

    then @FM@ is an alias for @FiniteMap@, and @FiniteMap@ is aliased by @FM@.
-}
module Curry.Frontend.Env.ModuleAlias ( AliasEnv, initAliasEnv, importAliases ) where

import qualified Data.Map   as Map (Map, empty, insert)
import           Data.Maybe        (fromMaybe)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax     (ImportDecl (..))

-- |Mapping from the original name of an imported module to its alias.
type AliasEnv = Map.Map ModuleIdent ModuleIdent

-- |Initial alias environment
initAliasEnv :: AliasEnv
initAliasEnv = Map.empty

-- |Create an alias environment from a list of import declarations
importAliases :: [ImportDecl] -> AliasEnv
importAliases = foldr bindAlias initAliasEnv

-- |Bind an alias for a module from a single import declaration
bindAlias :: ImportDecl -> AliasEnv -> AliasEnv
bindAlias (ImportDecl _ mid _ alias _) = Map.insert mid $ fromMaybe mid alias
