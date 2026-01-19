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
module Curry.Frontend.Env.Determinism
  (module Curry.Frontend.Env.Determinism, DetScheme(..))
  where

import Prelude hiding ( (<>) )
import Data.Map ( Map )
import qualified Data.Map as Map

import Curry.Base.Ident
import Curry.Frontend.Base.Types
import Curry.Base.Pretty ( Pretty(..), parens, dot, (<+>), (<>) )

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
               | II QualIdent QualIdent [Type] -- class, method, instance type
               | CI QualIdent QualIdent -- class, default method
  deriving (Eq, Ord, Show)

identInfoFun :: IdentInfo -> QualIdent
identInfoFun (QI meth) = meth
identInfoFun (II _ meth _) = meth
identInfoFun (CI _ meth) = meth

toClassIdent :: QualIdent -> IdentInfo -> IdentInfo
toClassIdent cls (QI qid) = CI cls (qid' { qidIdent = (qidIdent qid') { idUnique = 0 } })
  where qid' = case qidModule qid of
            Nothing -> qualifyLike cls (unqualify qid)
            Just _  -> qid
toClassIdent _ ii = ii

toInstanceIdent :: QualIdent -> [Type] -> IdentInfo -> IdentInfo
toInstanceIdent cls instTys (QI qid) =
  II qcls (qid { qidIdent = (qidIdent qid) { idUnique = 0 }
                                      , qidModule = qidModule qcls }) instTys
    where
      qcls | isQualified cls = cls
           | otherwise       = qualifyLike qid (unqualify cls)
toInstanceIdent _ _ ii = ii

instance Pretty IdentInfo where
  pPrint (QI qid) = pPrint qid
  pPrint (II cls tc meth) = parens (pPrint cls <+> pPrint tc) <> dot <> pPrint meth
  pPrint (CI cls meth) = pPrint cls <+> pPrint meth

instance Pretty DetEnv where
  pPrint = pPrint . Map.toList
