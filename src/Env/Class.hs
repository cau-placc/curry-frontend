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
  , minPredSet, maxPredSet
  ) where

import           Data.List       (nub, sort)
import qualified Data.Map       as Map (Map, empty, insertWith, lookup)
import qualified Data.Set.Extra as Set (Set, insert, delete, concatMap
                                       , union, difference, map, fromList)

import Base.Types
import Base.TypeSubst

import Curry.Base.Ident

import Base.Messages (internalError)

type ClassInfo = (Int, PredSet, [([Ident],[Ident])] ,[(Ident, Bool)])

type ClassEnv = Map.Map QualIdent ClassInfo

initClassEnv :: ClassEnv
initClassEnv = Map.empty

bindClassInfo :: QualIdent -> ClassInfo -> ClassEnv -> ClassEnv
bindClassInfo cls (arity, sclss, fds ,ms) =
  Map.insertWith mergeClassInfo cls (arity, sclss, fds, ms)

-- We have to be careful when merging two class infos into one as hidden class
-- declarations in interfaces provide no information about class methods. If
-- one of the method lists is empty, we simply take the other one. This way,
-- we do overwrite the list of class methods that may have been entered into
-- the class environment before with an empty list.

mergeClassInfo :: ClassInfo -> ClassInfo -> ClassInfo
mergeClassInfo (arity1, sclss1, fds1, ms1) (_, _, _, ms2) 
   = (arity1, sclss1, fds1, if null ms1 then ms2 else ms1)

lookupClassInfo :: QualIdent -> ClassEnv -> Maybe ClassInfo
lookupClassInfo = Map.lookup

arity :: QualIdent -> ClassEnv -> Int
arity cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (ar, _, _, _) -> ar
  _ -> internalError $ "Env.Class.arity: " ++ show cls

superClasses :: QualIdent -> ClassEnv -> PredSet
superClasses cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, sclss, _, _) -> sclss
  _ -> internalError $ "Env.Classes.superClasses: " ++ show cls

-- Taken from Leif-Erik Krueger's master thesis
allSuperClasses :: QualIdent -> ClassEnv -> PredSet
allSuperClasses cls clsEnv = allSuperClasses' $
  Pred Other cls $ map TypeVariable [0 .. arity cls clsEnv - 1]
 where
  allSuperClasses' pr@(Pred _ scls tys) =
    pr `Set.insert` Set.concatMap (allSuperClasses' . expandAliasType tys)
                                  (superClasses scls clsEnv)



funDeps :: QualIdent -> ClassEnv -> [([Ident], [Ident])]
funDeps cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, _, fds, _) -> fds
  Nothing -> internalError $ "Env.Class.funDeps: " ++ show cls

classMethods :: QualIdent -> ClassEnv -> [Ident]
classMethods cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, _, _, ms) -> map fst ms
  _ -> internalError $ "Env.Classes.classMethods: " ++ show cls

hasDefaultImpl :: QualIdent -> Ident -> ClassEnv -> Bool
hasDefaultImpl cls f clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, _, _, ms) -> case lookup f ms of
    Just dflt -> dflt
    Nothing -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show f
  _ -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show cls

minPredSet :: ClassEnv -> PredSet -> PredSet
minPredSet clsEnv ps =
  ps `Set.difference` Set.concatMap (impliedPreds clsEnv) ps

maxPredSet :: ClassEnv -> PredSet -> PredSet
maxPredSet clsEnv ps = 
  ps `Set.union` Set.concatMap (impliedPreds clsEnv) ps


impliedPreds :: ClassEnv -> Pred -> PredSet
impliedPreds clsEnv pr@(Pred _ cls tys) = Set.delete (Pred Other cls tys) $
  Set.map (expandAliasType tys) (allSuperClasses cls clsEnv)