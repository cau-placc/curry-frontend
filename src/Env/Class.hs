{- |
    Module      :  $Header$
    Description :  Environment of classes
    Copyright   :  (c) 2016 - 2020 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about all type classes in an
    environment that maps type classes to a sorted list of their direct
    superclasses and all their associated class methods with an additional
    flag stating whether an default implementation has been provided or not.
    For both the type class identifier and the list of super classes original
    names are used. Thus, the use of a flat environment is sufficient.
-}

module Env.Class
  ( ClassEnv, initClassEnv
  , ClassInfo, bindClassInfo, mergeClassInfo, lookupClassInfo
  , superClasses, allSuperClasses, classMethods, hasDefaultImpl
  ) where

import           Data.List       (nub, sort)
import qualified Data.Map as Map (Map, empty, insertWith, lookup)

import Curry.Base.Ident

import Base.Messages (internalError)

type ClassInfo = ([QualIdent], [(Ident, Bool)])

type ClassEnv = Map.Map QualIdent ClassInfo

initClassEnv :: ClassEnv
initClassEnv = Map.empty

bindClassInfo :: QualIdent -> ClassInfo -> ClassEnv -> ClassEnv
bindClassInfo cls (sclss, ms) =
  Map.insertWith mergeClassInfo cls (sort sclss, ms)

-- We have to be careful when merging two class infos into one as hidden class
-- declarations in interfaces provide no information about class methods. If
-- one of the method lists is empty, we simply take the other one. This way,
-- we do overwrite the list of class methods that may have been entered into
-- the class environment before with an empty list.

mergeClassInfo :: ClassInfo -> ClassInfo -> ClassInfo
mergeClassInfo (sclss1, ms1) (_, ms2) = (sclss1, if null ms1 then ms2 else ms1)

lookupClassInfo :: QualIdent -> ClassEnv -> Maybe ClassInfo
lookupClassInfo = Map.lookup

superClasses :: QualIdent -> ClassEnv -> [QualIdent]
superClasses cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (sclss, _) -> sclss
  _ -> internalError $ "Env.Classes.superClasses: " ++ show cls

allSuperClasses :: QualIdent -> ClassEnv -> [QualIdent]
allSuperClasses cls clsEnv = nub $ classes cls
  where
    classes cls' = cls' : concatMap classes (superClasses cls' clsEnv)

classMethods :: QualIdent -> ClassEnv -> [Ident]
classMethods cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, ms) -> map fst ms
  _ -> internalError $ "Env.Classes.classMethods: " ++ show cls

hasDefaultImpl :: QualIdent -> Ident -> ClassEnv -> Bool
hasDefaultImpl cls f clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, ms) -> case lookup f ms of
    Just dflt -> dflt
    Nothing -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show f
  _ -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show cls
