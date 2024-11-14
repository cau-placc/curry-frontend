{- |
    Module      :  $Header$
    Description :  Environment of type identifiers
    Copyright   :  (c) 2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    At the type level, we distinguish data and renaming types, synonym
    types, and type classes. Type variables are not recorded. Type
    synonyms use a kind of their own so that the compiler can verify that
    no type synonyms are used in type expressions in interface files.
-}

module Curry.Frontend.Env.Type
  ( TypeKind (..), toTypeKind,
    TypeEnv, bindTypeKind, lookupTypeKind, qualLookupTypeKind
  ) where

import Curry.Base.Ident

import Curry.Frontend.Base.Messages (internalError)
import Curry.Frontend.Base.TopEnv
import Curry.Frontend.Base.Types (constrIdent, methodName)

import Curry.Frontend.Env.TypeConstructor (TypeInfo (..))

import Data.List (union)

data TypeKind
  = Data  QualIdent [Ident]
  | Alias QualIdent
  | Class QualIdent [Ident]
  deriving (Eq, Show)

instance Entity TypeKind where
  origName (Data  tc  _) = tc
  origName (Alias tc   ) = tc
  origName (Class cls _) = cls

  merge (Data tc cs) (Data tc' cs')
    | tc == tc' = Just $ Data tc $ cs `union` cs'
  merge (Alias tc) (Alias tc')
    | tc == tc' = Just $ Alias tc
  merge (Class cls ms) (Class cls' ms')
    | cls == cls' = Just $ Class cls $ ms `union` ms'
  merge _ _ = Nothing

toTypeKind :: TypeInfo -> TypeKind
toTypeKind (DataType     tc    _ cs) = Data tc (map constrIdent cs)
toTypeKind (RenamingType tc    _ nc) = Data tc [constrIdent nc]
toTypeKind (AliasType    tc  _ _  _) = Alias tc
toTypeKind (TypeClass    cls   _ ms) = Class cls (map methodName ms)
toTypeKind (TypeVar               _) =
  internalError "Env.Type.toTypeKind: type variable"

type TypeEnv = TopEnv TypeKind

bindTypeKind :: ModuleIdent -> Ident -> TypeKind -> TypeEnv -> TypeEnv
bindTypeKind m ident tk = bindTopEnv ident tk . qualBindTopEnv qident tk
  where
    qident = qualifyWith m ident

lookupTypeKind :: Ident -> TypeEnv -> [TypeKind]
lookupTypeKind = lookupTopEnv

qualLookupTypeKind :: QualIdent -> TypeEnv -> [TypeKind]
qualLookupTypeKind = qualLookupTopEnv
