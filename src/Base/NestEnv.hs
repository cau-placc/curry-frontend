{- |
    Module      :  $Header$
    Description :  Nested Environments
    Copyright   :  (c) 1999 - 2003 Wolfgang Lux
                       2011 - 2015 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The 'NestEnv' environment type extends top-level environments  to manage
   nested scopes. Local scopes allow only for a single, unambiguous definition.

   As a matter of convenience, the module 'TopEnv' is exported by
   the module 'NestEnv'. Thus, only the latter needs to be imported.
-}

module Base.NestEnv
  ( module Base.TopEnv
  , NestEnv, emptyEnv, bindNestEnv, qualBindNestEnv
  , lookupNestEnv, qualLookupNestEnv
  , rebindNestEnv, qualRebindNestEnv
  , unnestEnv, toplevelEnv, globalEnv, nestEnv, elemNestEnv
  , qualModifyNestEnv, modifyNestEnv, localNestEnv, qualInLocalNestEnv
  ) where

import qualified Data.Map         as Map
import           Curry.Base.Ident

import Base.Messages (internalError)
import Base.TopEnv

data NestEnv a
  = GlobalEnv (TopEnv  a)
  | LocalEnv  (NestEnv a) (Map.Map Ident a)
    deriving Show

instance Functor NestEnv where
  fmap f (GlobalEnv     env) = GlobalEnv (fmap f  env)
  fmap f (LocalEnv genv env) = LocalEnv  (fmap f genv) (fmap f env)

globalEnv :: TopEnv a -> NestEnv a
globalEnv = GlobalEnv

emptyEnv :: NestEnv a
emptyEnv = globalEnv emptyTopEnv

nestEnv :: NestEnv a -> NestEnv a
nestEnv env = LocalEnv env Map.empty

unnestEnv :: NestEnv a -> NestEnv a
unnestEnv g@(GlobalEnv   _) = g
unnestEnv (LocalEnv genv _) = genv

toplevelEnv :: NestEnv a -> TopEnv a
toplevelEnv (GlobalEnv   env) = env
toplevelEnv (LocalEnv genv _) = toplevelEnv genv

bindNestEnv :: Ident -> a -> NestEnv a -> NestEnv a
bindNestEnv x y (GlobalEnv     env) = GlobalEnv $ bindTopEnv x y env
bindNestEnv x y (LocalEnv genv env) = case Map.lookup x env of
  Just  _ -> internalError $ "NestEnv.bindNestEnv: " ++ show x ++ " is already bound"
  Nothing -> LocalEnv genv $ Map.insert x y env

qualBindNestEnv :: QualIdent -> a -> NestEnv a -> NestEnv a
qualBindNestEnv x y (GlobalEnv     env) = GlobalEnv $ qualBindTopEnv x y env
qualBindNestEnv x y (LocalEnv genv env)
  | isQualified x = internalError $ "NestEnv.qualBindNestEnv " ++ show x
  | otherwise     = case Map.lookup x' env of
      Just  _ -> internalError $ "NestEnv.qualBindNestEnv " ++ show x
      Nothing -> LocalEnv genv $ Map.insert x' y env
    where x' = unqualify x

-- Rebinds a value to a variable, failes if the variable was unbound before
rebindNestEnv :: Ident -> a -> NestEnv a -> NestEnv a
rebindNestEnv = qualRebindNestEnv . qualify

qualRebindNestEnv :: QualIdent -> a -> NestEnv a -> NestEnv a
qualRebindNestEnv x y (GlobalEnv     env) = GlobalEnv $ qualRebindTopEnv x y env
qualRebindNestEnv x y (LocalEnv genv env)
  | isQualified x = internalError $ "NestEnv.qualRebindNestEnv " ++ show x
  | otherwise     = case Map.lookup x' env of
      Just  _ -> LocalEnv genv $ Map.insert x' y env
      Nothing -> LocalEnv (qualRebindNestEnv x y genv) env
    where x' = unqualify x

lookupNestEnv :: Ident -> NestEnv a -> [a]
lookupNestEnv x (GlobalEnv     env) = lookupTopEnv x env
lookupNestEnv x (LocalEnv genv env) = case Map.lookup x env of
  Just  y -> [y]
  Nothing -> lookupNestEnv x genv

qualLookupNestEnv :: QualIdent -> NestEnv a -> [a]
qualLookupNestEnv x env
  | isQualified x = qualLookupTopEnv x $ toplevelEnv env
  | otherwise     = lookupNestEnv (unqualify x) env

elemNestEnv :: Ident -> NestEnv a -> Bool
elemNestEnv x env = not (null (lookupNestEnv x env))

-- Applies a function to a value binding, does nothing if the variable is unbound
modifyNestEnv :: (a -> a) -> Ident -> NestEnv a -> NestEnv a
modifyNestEnv f = qualModifyNestEnv f . qualify

qualModifyNestEnv :: (a -> a) -> QualIdent -> NestEnv a -> NestEnv a
qualModifyNestEnv f x env = case qualLookupNestEnv x env of
  []    -> env
  y : _ -> qualRebindNestEnv x (f y) env

-- Returns the variables and values bound on the bottom (meaning non-top) scope
localNestEnv :: NestEnv a -> [(Ident, a)]
localNestEnv (GlobalEnv env)  = localBindings env
localNestEnv (LocalEnv _ env) = Map.toList env

-- Returns wether the variable is bound on the bottom (meaning non-top) scope
qualInLocalNestEnv :: QualIdent -> NestEnv a -> Bool
qualInLocalNestEnv x (GlobalEnv  env) = qualElemTopEnv x env
qualInLocalNestEnv x (LocalEnv _ env) = not (isQualified x)
                                        && Map.member (unqualify x) env
