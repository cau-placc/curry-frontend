{- |
    Module      :  $Header$
    Description :  Code generators
    Copyright   :  (c) 2011        Björn Peemöller
                       2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different code generators.
-}
module Generators where

import qualified Curry.AbstractCurry            as AC   (CurryProg)
import qualified Curry.FlatCurry.Type           as FC   (Prog, TypeExpr)
import qualified Curry.FlatCurry.Annotated.Type as AFC  (AProg)
import qualified Curry.FlatCurry.Typed.Type     as TFC  (TProg)
import qualified Curry.Syntax                   as CS   (Module)

import qualified Generators.GenAbstractCurry    as GAC   (genAbstractCurry)
import qualified Generators.GenFlatCurry        as GFC   ( genFlatCurry
                                                           , genFlatInterface
                                                           )
import qualified Generators.GenTypeAnnotatedFlatCurry
                                                as GTAFC (genTypeAnnotatedFlatCurry)
import qualified Generators.GenTypedFlatCurry   as GTFC  (genTypedFlatCurry)

import           Base.Types                          (Type, PredType)

import           CompilerEnv                         (CompilerEnv (..))
import qualified IL                                  (Module)

-- |Generate typed AbstractCurry
genTypedAbstractCurry :: CompilerEnv -> CS.Module PredType -> AC.CurryProg
genTypedAbstractCurry = GAC.genAbstractCurry False

-- |Generate untyped AbstractCurry
genUntypedAbstractCurry :: CompilerEnv -> CS.Module PredType -> AC.CurryProg
genUntypedAbstractCurry = GAC.genAbstractCurry True

-- |Generate typed FlatCurry
genTypedFlatCurry :: CompilerEnv -> CS.Module Type -> IL.Module
                  -> TFC.TProg
genTypedFlatCurry = GTFC.genTypedFlatCurry

-- |Generate type-annotated FlatCurry
genTypeAnnotatedFlatCurry :: CompilerEnv -> CS.Module Type -> IL.Module
                          -> AFC.AProg FC.TypeExpr
genTypeAnnotatedFlatCurry = GTAFC.genTypeAnnotatedFlatCurry

-- |Generate FlatCurry
genFlatCurry :: TFC.TProg -> FC.Prog
genFlatCurry = GFC.genFlatCurry

-- |Generate a FlatCurry interface
genFlatInterface :: FC.Prog -> FC.Prog
genFlatInterface = GFC.genFlatInterface
