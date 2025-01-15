{- |
    Module      :  $Header$
    Description :  Environment of imported interfaces
    Copyright   :  (c) 2002 - 2004 Wolfgang Lux
                       2011 - 2013 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides an environment for imported interfaces.
-}
module Curry.Frontend.Env.Interface where

import qualified Data.Map as Map (Map, empty, lookup)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax     (Interface)

-- |Environment which maps the 'ModuleIdent' of an imported module
-- to the corresponding 'Interface'.
type InterfaceEnv = Map.Map ModuleIdent Interface

-- |Initial 'InterfaceEnv'.
initInterfaceEnv :: InterfaceEnv
initInterfaceEnv = Map.empty

-- |Lookup the 'Interface' for an imported module.
lookupInterface :: ModuleIdent -> InterfaceEnv -> Maybe Interface
lookupInterface = Map.lookup
