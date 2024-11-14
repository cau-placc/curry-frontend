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
import Curry.FlatCurry.Annotated.Goodies
import Curry.FlatCurry.Annotated.Type

-- transforms annotated FlatCurry code to FlatCurry code
genFlatCurry :: AProg TypeExpr -> Prog
genFlatCurry = trAProg
  (\name imps types funcs ops ->
    Prog name imps types (map genFlatFuncDecl funcs) ops)

genFlatFuncDecl :: AFuncDecl TypeExpr -> FuncDecl
genFlatFuncDecl = trAFunc
  (\name arity vis ty rule -> Func name arity vis ty $ genFlatRule rule)

genFlatRule :: ARule TypeExpr -> Rule
genFlatRule = trARule
  (\_ args e -> Rule (map fst args) $ genFlatExpr e)
  (const External)

genFlatExpr :: AExpr TypeExpr -> Expr
genFlatExpr = trAExpr
  (const Var)
  (const Lit)
  (\_ ct (name, _) args -> Comb ct name args)
  (const $ Let . map (\(v, e') -> (fst v, e')))
  (const $ Free . map fst)
  (const Or)
  (const Case)
  (Branch . genFlatPattern)
  (const Typed)

genFlatPattern :: APattern TypeExpr -> Pattern
genFlatPattern = trAPattern
  (\_ (name, _) args -> Pattern name $ map fst args)
  (const LPattern)

-- transforms a FlatCurry module to a FlatCurry interface
genFlatInterface :: Prog -> Prog
genFlatInterface =
  updProgFuncs $ map $ updFuncRule $ const $ Rule [] $ Var 0
