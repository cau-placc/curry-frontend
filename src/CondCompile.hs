{- |
    Module      :  $Header$
    Description :  Conditional compilation
    Copyright   :  (c)        2017 Finn Teegen
                   (c) 2017 - 2023 Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de TODO: update everywhere
    Stability   :  experimental
    Portability :  portable

    This module wraps the conditional compiling transformation,
    so that it can be used in the compilation monad of the frontend.
-}

module CondCompile (condCompile) where

import Curry.Base.Monad
import Curry.CondCompile.Transform (condTransform)

import CompilerOpts (CppOpts (..))

condCompile :: CppOpts -> FilePath -> String -> CYIO String
condCompile opts fn p
  | not (cppRun opts) = return p
  | otherwise         = either (failMessages . (: []))
                               ok
                               (condTransform (cppDefinitions opts) fn p)
