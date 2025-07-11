{- |
    Module      :  $Header$
    Description :  Different checks on a Curry module
    Copyright   :  (c) 2011 - 2013 Björn Peemöller
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different checks to be performed on a Curry
    module during compilation, e.g. type checking.
-}
module Curry.Frontend.Checks where

import qualified Curry.Frontend.Checks.CaseModeCheck     as CMC (caseModeCheck)
import qualified Curry.Frontend.Checks.InstanceCheck     as INC (instanceCheck)
import qualified Curry.Frontend.Checks.InterfaceCheck    as IC  (interfaceCheck)
import qualified Curry.Frontend.Checks.ImportSyntaxCheck as ISC (importCheck)
import qualified Curry.Frontend.Checks.DeriveCheck       as DC  (deriveCheck)
import qualified Curry.Frontend.Checks.ExportCheck       as EC  (exportCheck, expandExports)
import qualified Curry.Frontend.Checks.ExtensionCheck    as EXC (extensionCheck)
import qualified Curry.Frontend.Checks.KindCheck         as KC  (kindCheck)
import qualified Curry.Frontend.Checks.PrecCheck         as PC  (precCheck)
import qualified Curry.Frontend.Checks.SyntaxCheck       as SC  (syntaxCheck)
import qualified Curry.Frontend.Checks.TypeCheck         as TC  (typeCheck)
import qualified Curry.Frontend.Checks.TypeSyntaxCheck   as TSC (typeSyntaxCheck)
import qualified Curry.Frontend.Checks.WarnCheck         as WC  (warnCheck)

import Curry.Base.Monad
import Curry.Syntax (Module (..), Interface (..), ImportSpec)

import Curry.Frontend.Base.Messages
import Curry.Frontend.Base.Types

import Curry.Frontend.CompilerEnv
import Curry.Frontend.CompilerOpts

type Check m a = Options -> CompEnv a -> CYT m (CompEnv a)

caseModeCheck :: Monad m => Check m (Module a)
caseModeCheck opts (env, mdl) = warnOrFailMessages (optWarnOpts opts) warns >> result
  where (warns, errs) = CMC.caseModeCheck (optCaseMode opts) mdl
        result | null errs = ok (env, mdl)
               | otherwise = failMessages errs

interfaceCheck :: Monad m => Check m Interface
interfaceCheck _ (env, intf)
  | null msgs = ok (env, intf)
  | otherwise = failMessages msgs
  where msgs = IC.interfaceCheck (opPrecEnv env) (tyConsEnv env) (classEnv env)
                                 (instEnv env) (valueEnv env) intf

importCheck :: Monad m => Interface -> Maybe ImportSpec
            -> CYT m (Maybe ImportSpec)
importCheck intf is
  | null msgs = ok is'
  | otherwise = failMessages msgs
  where (is', msgs) = ISC.importCheck intf is

-- |Check for enabled language extensions.
--
-- * Declarations: remain unchanged
-- * Environment:  The enabled language extensions are updated
extensionCheck :: Monad m => Check m (Module a)
extensionCheck opts (env, mdl)
  | null msgs = ok (env { extensions = exts }, mdl)
  | otherwise = failMessages msgs
  where (exts, msgs) = EXC.extensionCheck opts mdl

-- |Check the type syntax of type definitions and signatures.
--
-- * Declarations: Nullary type constructors and type variables are
--                 disambiguated
-- * Environment:  remains unchanged
typeSyntaxCheck :: Monad m => Check m (Module a)
typeSyntaxCheck _ (env, mdl)
  | null msgs = ok (env, mdl')
  | otherwise = failMessages msgs
  where (mdl', msgs) = TSC.typeSyntaxCheck (extensions env) (tyConsEnv env)
                                           (classEnv env) mdl

-- |Check the kinds of type definitions and signatures.
--
-- * Declarations: remain unchanged
-- * Environment:  The type constructor and class environment are updated
kindCheck :: Monad m => Check m (Module a)
kindCheck _ (env, mdl)
  | null msgs = ok (env { tyConsEnv = tcEnv', classEnv = clsEnv' }, mdl)
  | otherwise = failMessages msgs
  where ((tcEnv', clsEnv'), msgs) = KC.kindCheck (tyConsEnv env) (classEnv env)
                                                 mdl

-- |Check for a correct syntax.
--
-- * Declarations: Nullary data constructors and variables are
--                 disambiguated, variables are renamed
-- * Environment:  remains unchanged
syntaxCheck :: Monad m => Check m (Module ())
syntaxCheck _ (env, mdl)
  | null msgs = ok (env { extensions = exts }, mdl')
  | otherwise = failMessages msgs
  where ((mdl', exts), msgs) = SC.syntaxCheck (extensions env) (tyConsEnv env)
                                              (valueEnv env) mdl

-- |Check the precedences of infix operators.
--
-- * Declarations: Expressions are reordered according to the specified
--                 precedences
-- * Environment:  The operator precedence environment is updated
precCheck :: Monad m => Check m (Module a)
precCheck _ (env, Module spi li ps m es is ds)
  | null msgs = ok (env { opPrecEnv = pEnv' }, Module spi li ps m es is ds')
  | otherwise = failMessages msgs
  where (ds', pEnv', msgs) = PC.precCheck (moduleIdent env) (opPrecEnv env) ds

-- |Check the deriving clauses.
--
-- * Declarations: remain unchanged
-- * Environment:  remain unchanged
deriveCheck :: Monad m => Check m (Module a)
deriveCheck _ (env, mdl) = case DC.deriveCheck (tyConsEnv env) mdl of
  msgs | null msgs -> ok (env, mdl)
       | otherwise -> failMessages msgs

-- |Check the instances.
--
-- * Declarations: remain unchanged
-- * Environment:  The instance environment is updated
instanceCheck :: Monad m => Check m (Module a)
instanceCheck _ (env, Module spi li ps m es is ds)
  | null msgs = ok (env { instEnv = inEnv' }, Module spi li ps m es is ds)
  | otherwise = failMessages msgs
  where (inEnv', msgs) = INC.instanceCheck (extensions env) (moduleIdent env)
                                           (tyConsEnv env) (classEnv env)
                                           (instEnv env) ds

-- |Apply the correct typing of the module.
--
-- * Declarations: Type annotations are added to all expressions.
-- * Environment:  The value environment is updated.
typeCheck :: Monad m => Options -> CompEnv (Module a)
          -> CYT m (CompEnv (Module PredType))
typeCheck _ (env, Module spi li ps m es is ds)
  | null msgs = ok (env { valueEnv = vEnv' }, Module spi li ps m es is ds')
  | otherwise = failMessages msgs
  where (ds', vEnv', msgs) = TC.typeCheck (extensions env) (moduleIdent env)
                                          (tyConsEnv env) (valueEnv env)
                                          (classEnv env) (instEnv env) ds

-- |Check the export specification
exportCheck :: Monad m => Check m (Module a)
exportCheck _ (env, mdl@(Module _ _ _ _ es _ _))
  | null msgs = ok (env, mdl)
  | otherwise = failMessages msgs
  where msgs = EC.exportCheck (moduleIdent env) (aliasEnv env)
                              (tyConsEnv env) (valueEnv env) es

-- |Check the export specification
expandExports :: Monad m => Options -> CompEnv (Module a) -> m (CompEnv (Module a))
expandExports _ (env, Module spi li ps m es is ds)
  = return (env, Module spi li ps m (Just es') is ds)
  where es' = EC.expandExports (moduleIdent env) (aliasEnv env)
                               (tyConsEnv env) (valueEnv env) es

-- |Check for warnings.
warnCheck :: Options -> CompilerEnv -> Module a -> [Message]
warnCheck opts env = WC.warnCheck (optWarnOpts opts)
  (aliasEnv env) (valueEnv env) (tyConsEnv env) (classEnv env)
