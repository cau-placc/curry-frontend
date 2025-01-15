{- |
    Module      :  $Header$
    Description :  Conditional compilation
    Copyright   :  (c)        2017 Finn Teegen
    Copyright   :  (c)   2018-2024 Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module handles conditional compilation by selectively transforming
    source code based on specified preprocessor directives.
-}

module Curry.Frontend.CondCompile (condCompile) where

import Curry.Base.Monad
import Curry.CondCompile.Transform (condTransform)

import Curry.Frontend.CompilerOpts (CppOpts (..))

condCompile :: CppOpts -> FilePath -> String -> CYIO String
condCompile opts fn p
  | not (cppRun opts) = return p
  | otherwise         = either (failMessages . (: []))
                               ok
                               (condTransform (cppDefinitions opts) fn p)
