{- |
    Module      :  $Header$
    Description :  Code generators
    Copyright   :  (c) 2011        Björn Peemöller
                       2017        Finn Teegen
                       2018        Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different code generators.
-}
module Curry.Frontend.Generators where

import Data.ByteString.Lazy
import Data.Binary

import qualified Curry.AbstractCurry            as AC   (CurryProg)
import qualified Curry.FlatCurry.Type           as FC   (Prog, TypeExpr)
import qualified Curry.FlatCurry.Annotated.Type as AFC  (AProg)
import qualified Curry.FlatCurry.Typed.Type     as TFC  (TProg)
import qualified Curry.Syntax                   as CS   (Module)

import qualified Curry.Frontend.Generators.GenAbstractCurry
                                                as GAC  (genAbstractCurry)
import qualified Curry.Frontend.Generators.GenFlatCurry
                                                as GFC  ( genFlatCurry
                                                        , genFlatInterface
                                                        )
import qualified Curry.Frontend.Generators.GenAnnotatedFlatCurry
                                                as GAFC (genAnnotatedFlatCurry)
import qualified Curry.Frontend.Generators.GenTypedFlatCurry
                                                as GTFC (genTypedFlatCurry)

import           Curry.Frontend.Base.Types              (Type, PredType)

import           Curry.Frontend.CompilerEnv             (CompilerEnv (..))
import qualified Curry.Frontend.IL              as IL   (Module)

-- |Generate typed AbstractCurry
genTypedAbstractCurry :: CompilerEnv -> CS.Module PredType -> AC.CurryProg
genTypedAbstractCurry = GAC.genAbstractCurry False

-- |Generate untyped AbstractCurry
genUntypedAbstractCurry :: CompilerEnv -> CS.Module PredType -> AC.CurryProg
genUntypedAbstractCurry = GAC.genAbstractCurry True

-- |Generate typed FlatCurry
genTypedFlatCurry :: AFC.AProg FC.TypeExpr -> TFC.TProg
genTypedFlatCurry = GTFC.genTypedFlatCurry

-- |Generate typed FlatCurry
genTypedBinaryFlatCurry :: AFC.AProg FC.TypeExpr -> ByteString
genTypedBinaryFlatCurry = encode . GTFC.genTypedFlatCurry

-- |Generate type-annotated FlatCurry
genAnnotatedFlatCurry :: Bool -> CompilerEnv -> CS.Module Type -> IL.Module
                      -> AFC.AProg FC.TypeExpr
genAnnotatedFlatCurry = GAFC.genAnnotatedFlatCurry

-- |Generate FlatCurry
genFlatCurry :: AFC.AProg FC.TypeExpr -> FC.Prog
genFlatCurry = GFC.genFlatCurry

-- |Generate a FlatCurry interface
genFlatInterface :: FC.Prog -> FC.Prog
genFlatInterface = GFC.genFlatInterface
