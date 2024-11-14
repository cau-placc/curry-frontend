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
module IL ( module IL.Type, module IL.Typing, ppModule, showModule ) where

import IL.Pretty     (ppModule)
import IL.ShowModule (showModule)
import IL.Type
import IL.Typing
