{- |
    Module      :  $Header$
    Description :  Code transformations
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different transformations of the source code.
-}
module Transformations where

import Curry.Syntax

import Base.Types

import Transformations.CaseCompletion as CC (completeCase)
import Transformations.CurryToIL      as IL (ilTrans, transType)
import Transformations.Derive         as DV (derive)
import Transformations.Desugar        as DS (desugar)
import Transformations.Dictionary     as DI (insertDicts)
import Transformations.Lift           as L  (lift)
import Transformations.Newtypes       as NT (removeNewtypes)
import Transformations.Qual           as Q  (qual)
import Transformations.Simplify       as S  (simplify)

import Env.TypeConstructor

import CompilerEnv
import Imports (qualifyEnv)
import qualified IL

-- |Fully qualify used constructors and functions.
qual :: CompEnv (Module a) -> CompEnv (Module a)
qual (env, mdl) = (qualifyEnv env, mdl')
  where mdl' = Q.qual (moduleIdent env) (tyConsEnv env) (valueEnv env) mdl

-- |Automatically derive instances.
derive :: CompEnv (Module PredType) -> CompEnv (Module PredType)
derive (env, mdl) = (env, mdl')
  where mdl' = DV.derive (tyConsEnv env) (valueEnv env) (instEnv env)
                         (opPrecEnv env) mdl

-- |Remove any syntactic sugar, changes the value environment.
desugar :: CompEnv (Module PredType) -> CompEnv (Module PredType)
desugar (env, mdl) = (env { valueEnv = tyEnv' }, mdl')
  where (mdl', tyEnv') = DS.desugar (extensions env) (valueEnv env)
                                    (tyConsEnv env) mdl

-- |Insert dictionaries, changes the type constructor and value environments.
insertDicts :: Bool -> CompEnv (Module PredType) -> CompEnv (Module Type)
insertDicts inlDi (env, mdl) = (env { interfaceEnv = intfEnv'
                                    , tyConsEnv = tcEnv'
                                    , valueEnv = vEnv'
                                    , opPrecEnv = pEnv' }, mdl')
  where (mdl', intfEnv', tcEnv', vEnv', pEnv') =
          DI.insertDicts inlDi (interfaceEnv env) (tyConsEnv env)
                         (valueEnv env) (classEnv env) (instEnv env)
                         (opPrecEnv env) mdl

-- |Remove newtype constructors.
removeNewtypes :: Bool -> CompEnv (Module Type) -> CompEnv (Module Type)
removeNewtypes remNT (env, mdl) = (env, mdl')
  where mdl' = NT.removeNewtypes remNT (valueEnv env) mdl

-- |Simplify the source code, changes the value environment.
simplify :: CompEnv (Module Type) -> CompEnv (Module Type)
simplify (env, mdl) = (env { valueEnv = tyEnv' }, mdl')
  where (mdl', tyEnv') = S.simplify (valueEnv env) mdl

-- |Lift local declarations, changes the value environment.
lift :: CompEnv (Module Type) -> CompEnv (Module Type)
lift (env, mdl) = (env { valueEnv = tyEnv' }, mdl')
  where (mdl', tyEnv') = L.lift (valueEnv env) mdl

-- |Translate into the intermediate language
ilTrans :: CompEnv (Module Type) -> CompEnv IL.Module
ilTrans (env, mdl) = (env, il)
  where il = IL.ilTrans (valueEnv env) (tyConsEnv env) mdl

transType :: TCEnv -> Type -> IL.Type
transType = IL.transType

-- |Add missing case branches
completeCase :: CompEnv IL.Module -> CompEnv IL.Module
completeCase (env, mdl) =
  (env, CC.completeCase (interfaceEnv env) (tyConsEnv env) mdl)
