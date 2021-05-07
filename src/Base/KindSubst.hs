{- |
    Module      :  $Header$
    Description :  Kind substitution
    Copyright   :  (c) 2016      Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements substitutions on kinds.
-}

module Base.KindSubst
  ( module Base.KindSubst, idSubst, singleSubst, bindSubst, compose
  ) where

import Base.Kinds
import Base.Subst
import Base.TopEnv

import Env.TypeConstructor

type KindSubst = Subst Int Kind

class SubstKind a where
  subst :: KindSubst -> a -> a

bindVar :: Int -> Kind -> KindSubst -> KindSubst
bindVar kv k = compose (bindSubst kv k idSubst)

substVar :: KindSubst -> Int -> Kind
substVar = substVar' KindVariable subst

instance SubstKind Kind where
  subst _     KindStar             = KindStar
  subst sigma (KindVariable    kv) = substVar sigma kv
  subst sigma (KindArrow    k1 k2) = KindArrow (subst sigma k1) (subst sigma k2)

instance SubstKind TypeInfo where
  subst theta (DataType     tc k cs) = DataType tc (subst theta k) cs
  subst theta (RenamingType tc k nc) = RenamingType tc (subst theta k) nc
  subst theta (AliasType  tc k n ty) = AliasType tc (subst theta k) n ty
  subst theta (TypeClass  cls ks ms) = TypeClass cls (map (subst theta) ks) ms
  subst theta (TypeVar            k) = TypeVar (subst theta k)

instance SubstKind a => SubstKind (TopEnv a) where
  subst = fmap . subst
