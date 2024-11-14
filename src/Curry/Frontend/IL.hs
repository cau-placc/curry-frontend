{- |
    Module      :  $Header$
    Description :  Intermediate language
    Copyright   :  (c) 2014, Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module is a simple re-export of the definition of the AST of IL
    and the pretty-printing of IL modules.
-}
module Curry.Frontend.IL
  ( module Curry.Frontend.IL.Type
  , module Curry.Frontend.IL.Typing
  , ppModule, showModule
  ) where

import Curry.Frontend.IL.Pretty     (ppModule)
import Curry.Frontend.IL.ShowModule (showModule)
import Curry.Frontend.IL.Type
import Curry.Frontend.IL.Typing
