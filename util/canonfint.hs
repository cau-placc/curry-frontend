{- |
    Module      :  $Header$
    Description :  Executable to fix FlatCurry interface files
    Copyright   :  (c) 2016 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This executable should be invoked as @canonfint old.fint new.fint@
    to read the FlatCurry interface file @old.fint@,
    convert the declarations inside to a canonical representation (see below),
    and emit the fixed interface into @new.fint@.

    The conversion performs the following changes:

    * Imports are lexicographically sorted
    * Type declarations are restricted to public declarations
      and lexicographically sorted
    * the body of external function declarations is represented
      as @Rule [] (Var 0)@, so that internally and externally defined
      functions are not distinguished in interface files
    * The type variables in reexported functions are renumbered to start from 0
    * Operator declarations are filtered for public operators and precendences
      that deviate from the default precendence
    * Operator declarations are lexicographically sorted

    This utility has been developed to aid the rewriting of the FlatCurry
    interface generation, to make new and old interface files comparable.
-}
module Main where

import Data.Function (on)
import Data.List (nub, sort, sortBy)
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.FilePath (takeDirectory)
import Curry.ExtendedFlat.Type
import Curry.ExtendedFlat.Goodies

main :: IO ()
main = do
  [f1, f2] <- getArgs
  mbFlat <- readFlat f1
  case mbFlat of
    Nothing  -> putStrLn $ "Could not read file " ++ f1
    Just fcy -> do
      createDirectoryIfMissing True (takeDirectory f2)
      writeFlatCurry f2 $ fixDecls fcy

fixDecls :: Prog -> Prog
fixDecls (Prog m is ts fs os) = Prog m (sort is) ts' fs' os'
  where
  ts' = sortBy (compare `on` typeName)
      $ filter (isPublic . typeVisibility) ts
  fs' = sortBy (compare `on` funcName)
      $ map (updFuncType fixTypeVars . changeExternal) fs
  os' = sortBy (compare `on` opName  )
      $ filter (not . isDefaultPrec)
      $ filter (isPublicOp fs) os
  isPublic p = p == Public
  changeExternal = updFuncRule (const (Rule [] (Var 0)))

  fixTypeVars ty = rnmAllVarsInTypeExpr rnm ty
    where
    rnm v = case lookup v sub of
      Just v' -> v'
      _       -> error "normType"
    sub = zip (nub $ allVarsInTypeExpr ty) [0 ..]

  isDefaultPrec od = opFixity od == InfixlOp && opPrecedence od == 9

  isPublicOp fs o = not $ null [ () | f <- fs
                                    , funcName f == opName o
                                    , isPublic (funcVisibility f)
                               ]
