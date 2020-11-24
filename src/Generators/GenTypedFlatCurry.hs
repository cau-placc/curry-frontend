{- |
    Module      :  $Header$
    Description :  Generation of typed FlatCurry program terms
    Copyright   :  (c) 2017        Finn Teegen
                       2018        Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of a typed 'FlatCurry' program term
    for a given module in the intermediate language.
-}
{-# LANGUAGE CPP #-}
module Generators.GenTypedFlatCurry (genTypedFlatCurry) where

import Curry.FlatCurry.Annotated.Type
import Curry.FlatCurry.Annotated.Goodies
import Curry.FlatCurry.Typed.Type

-- transforms annotated FlatCurry code to typed FlatCurry code
genTypedFlatCurry :: AProg TypeExpr -> TProg
genTypedFlatCurry = trAProg
  (\name imps types funcs ops ->
    TProg name imps types (map genTypedFuncDecl funcs) ops)

genTypedFuncDecl :: AFuncDecl TypeExpr -> TFuncDecl
genTypedFuncDecl = trAFunc
  (\name arity vis ty rule -> TFunc name arity vis ty $ genTypedRule rule)

genTypedRule :: ARule TypeExpr -> TRule
genTypedRule = trARule
  (\_ args e -> TRule args $ genTypedExpr e)
  TExternal

genTypedExpr :: AExpr TypeExpr -> TExpr
genTypedExpr = trAExpr
  TVarE
  TLit
  (\ty ct (name, _) args -> TComb ty ct name args)
  (const TLet)
  (const TFree)
  (const TOr)
  (const TCase)
  (TBranch . genTypedPattern)
  (const TTyped)

genTypedPattern :: APattern TypeExpr -> TPattern
genTypedPattern = trAPattern
  (\ty (name, _) args -> TPattern ty name args)
  TLPattern

