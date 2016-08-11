{- |
    Module      :  $Header$
    Description :  Environment of classes
    Copyright   :  (c) 2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about all type classes in an
    environment that maps type classes to a list of their direct
    superclasses and all their associated class methods. For both
    the type class identifier and the list of super classes original
    names are used. Thus, the use of a flat environment is sufficient.
-}

module Env.Class
  ( ClassEnv, initClassEnv
  , ClassInfo, bindClassInfo, lookupClassInfo
  , superClasses, allSuperClasses, classMethods
  ) where

import           Data.List       (nub)
import qualified Data.Map as Map (Map, empty, insertWith, lookup)

import Curry.Base.Ident

import Base.Messages (internalError)

type ClassInfo = ([QualIdent], [Ident])

type ClassEnv = Map.Map QualIdent ClassInfo

initClassEnv :: ClassEnv
initClassEnv = Map.empty

bindClassInfo :: QualIdent -> ClassInfo -> ClassEnv -> ClassEnv
bindClassInfo = Map.insertWith mergeClassInfo

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
  Just (_, ms) -> ms
  _ -> internalError $ "Env.Classes.classMethods: " ++ show cls
