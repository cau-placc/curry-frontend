{- |
    Module      :  $Header$
    Description :  Conditional compilation
    Copyright   :  (c)        2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    TODO
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
