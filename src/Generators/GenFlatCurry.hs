{- |
    Module      :  $Header$
    Description :  Generation of FlatCurry program and interface terms
    Copyright   :  (c) 2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of a 'FlatCurry' program term or
    a 'FlatCurry' interface out of an 'Annotated FlatCurry' module.
-}
module Generators.GenFlatCurry (genFlatCurry, genFlatInterface) where

import Curry.FlatCurry.Goodies
import Curry.FlatCurry.Type
import Curry.FlatCurry.Typed.Goodies
import Curry.FlatCurry.Typed.Type

-- transforms annotated FlatCurry code to FlatCurry code
genFlatCurry :: TProg -> Prog
genFlatCurry = trTProg
  (\name imps types funcs ops ->
    Prog name imps types (map genFlatFuncDecl funcs) ops)

genFlatFuncDecl :: TFuncDecl -> FuncDecl
genFlatFuncDecl = trTFunc
  (\name arity vis ty rule -> Func name arity vis ty $ genFlatRule rule)

genFlatRule :: TRule -> Rule
genFlatRule = trTRule
  (\args e -> Rule (map fst args) $ genFlatExpr e)
  (const External)

genFlatExpr :: TExpr -> Expr
genFlatExpr = trTExpr
  (const Var)
  (const Lit)
  (\_ ct name args -> Comb ct name args)
  (\bs e -> Let (map (\(v, e') -> (fst v, e')) bs) e)
  (\vs e -> Free (map fst vs) e)
  Or
  Case
  (\pat e -> Branch (genFlatPattern pat) e)
  Typed

genFlatPattern :: TPattern -> Pattern
genFlatPattern = trTPattern
  (\_ name args -> Pattern name $ map fst args)
  (const LPattern)

-- transforms a FlatCurry module to a FlatCurry interface
genFlatInterface :: Prog -> Prog
genFlatInterface =
  updProgFuncs $ map $ updFuncRule $ const $ Rule [] $ Var 0
