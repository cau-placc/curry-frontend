{- |
    Module      :  $Header$
    Description :  Environment of determinism types
    Copyright   :  (c) 2023 - 2023 Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about all determinism types
    in a flat environment that maps special identifier to their determinism scheme.
    Such a special identifier can be one of the following:
     - an ordinary qualified identifier,
     - a type class default method implementation with its qualified class and method identifiers
     - a instance method impllementation with its qualified class, type constructor and method identifiers

    This module additionally defines a nested environment that is used
    during the determinism inference and check.
-}
{-# LANGUAGE FlexibleInstances    #-}
module Env.Determinism where

import Prelude hiding ( (<>) )
import Data.Map ( Map )
import qualified Data.Map as Map

import Base.Messages ( internalError )
import Base.TopEnv (origName)
import Base.Types ( DetScheme(..) )
import Curry.Base.Ident
import Curry.Base.Pretty ( Pretty(..), parens, dot, (<+>), (<>) )
import Curry.Syntax ( TypeExpr(..), InstanceType )
import Env.TypeConstructor (TCEnv, qualLookupTypeInfo)

type DetEnv = Map IdentInfo DetScheme

type TopDetEnv = DetEnv

initDetEnv :: DetEnv
initDetEnv = Map.empty

lookupDetEnv :: QualIdent -> DetEnv -> Maybe DetScheme
lookupDetEnv = Map.lookup . QI

data NestDetEnv = Top TopDetEnv
                | LocalEnv NestDetEnv DetEnv

lookupNestDetEnv :: IdentInfo -> NestDetEnv -> Maybe DetScheme
lookupNestDetEnv ii (Top env) = Map.lookup ii env
lookupNestDetEnv ii (LocalEnv env lcl) = case Map.lookup ii lcl of
  Just ty -> Just ty
  Nothing -> lookupNestDetEnv ii env

bindNestDetEnv :: IdentInfo -> DetScheme -> NestDetEnv -> NestDetEnv
bindNestDetEnv ii ty (Top env) = Top (Map.insert ii ty env)
bindNestDetEnv ii ty (LocalEnv inner lcl) = LocalEnv inner (Map.insert ii ty lcl)

nestDetEnv :: NestDetEnv -> NestDetEnv
nestDetEnv env = LocalEnv env Map.empty

unnestDetEnv :: NestDetEnv -> NestDetEnv
unnestDetEnv (Top env) = Top env
unnestDetEnv (LocalEnv env _) = env

extractTopDetEnv :: NestDetEnv -> TopDetEnv
extractTopDetEnv (Top env) = env
extractTopDetEnv (LocalEnv env _) = extractTopDetEnv env

mapNestDetEnv :: (DetScheme -> DetScheme) -> NestDetEnv -> NestDetEnv
mapNestDetEnv f (Top env) = Top (Map.map f env)
mapNestDetEnv f (LocalEnv env lcl) = LocalEnv (mapNestDetEnv f env) (Map.map f lcl)

flattenNestDetEnv :: NestDetEnv -> DetEnv
flattenNestDetEnv (Top env) = env
flattenNestDetEnv (LocalEnv env lcl) = Map.union lcl (flattenNestDetEnv env)

data IdentInfo = QI QualIdent
               -- class, tycon, method (only for known instances with the given type constructor)
               | II QualIdent QualIdent QualIdent
               | CI QualIdent QualIdent -- class, default method
  deriving (Eq, Ord, Show)

identInfoFun :: IdentInfo -> QualIdent
identInfoFun (QI meth) = meth
identInfoFun (II _ _ meth) = meth
identInfoFun (CI _ meth) = meth

toClassIdent :: QualIdent -> IdentInfo -> IdentInfo
toClassIdent cls (QI qid) = CI cls (qid' { qidIdent = (qidIdent qid') { idUnique = 0 } })
  where qid' = case qidModule qid of
            Nothing -> qualifyLike cls (unqualify qid)
            Just _  -> qid
toClassIdent _ ii = ii

toInstanceIdent :: ModuleIdent -> TCEnv -> QualIdent -> InstanceType -> IdentInfo -> IdentInfo
toInstanceIdent mid tcE cls ty ii = case toInstanceIdentMaybe mid tcE cls ty ii of
  Just ii' -> ii'
  Nothing  -> internalError (show ty ++ " is not a constructor type")

toInstanceIdentMaybe :: ModuleIdent -> TCEnv -> QualIdent -> InstanceType -> IdentInfo -> Maybe IdentInfo
toInstanceIdentMaybe mid tcE cls ty (QI qid) = case ty of
  ConstructorType _ tc ->
    Just $ II qcls qtc (qid { qidIdent = (qidIdent qid) { idUnique = 0 }
                            , qidModule = qidModule qcls })
    where
      qcls | isQualified cls = cls
           | otherwise       = qualifyLike qid (unqualify cls)
      qtc = case qualLookupTypeInfo tc tcE of
        [i] -> qualQualify mid (origName i)
        _ | unqualify tc == listId   -> qualQualify preludeMIdent tc
          | unqualify tc == unitId   -> qualQualify preludeMIdent tc
          | unqualify tc == arrowId  -> qualQualify preludeMIdent tc
          | isTupleId (unqualify tc) -> qualQualify preludeMIdent tc
          | otherwise                -> internalError $ "Env.Determinism: " ++ show tc ++ " not found"
  ListType sp _ -> toInstanceIdentMaybe mid tcE cls (ConstructorType sp qList) (QI qid)
    where qList = qualifyWith preludeMIdent listId
  TupleType sp args -> toInstanceIdentMaybe mid tcE cls (ConstructorType sp qTuple) (QI qid)
    where qTuple = qualQualify preludeMIdent (qTupleId (length args))
  ArrowType sp _ _ -> toInstanceIdentMaybe mid tcE cls (ConstructorType sp qArrowId) (QI qid)
  ParenType _ ty' -> toInstanceIdentMaybe mid tcE cls ty' (QI qid)
  ApplyType _ ty' _ -> toInstanceIdentMaybe mid tcE cls ty' (QI qid)
  _ -> Nothing
toInstanceIdentMaybe _ _ _ _ ii = Just ii

instance Pretty IdentInfo where
  pPrint (QI qid) = pPrint qid
  pPrint (II cls tc meth) = parens (pPrint cls <+> pPrint tc) <> dot <> pPrint meth
  pPrint (CI cls meth) = pPrint cls <+> pPrint meth

instance Pretty DetEnv where
  pPrint = pPrint . Map.toList
