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
  , superClasses, allSuperClasses, visibleClassMethods, allClassMethods
  , hasDefaultImpl, getDeterminismAnnotation
  , minPredSet, maxPredSet
  ) where

import           Data.List       (nub, sort)
import qualified Data.Map as Map (Map, empty, insertWith, lookup)
import qualified Data.Set.Extra as Set

import Curry.Base.Ident

import Base.Messages (internalError)
import Base.Types (DetScheme, PredSet, Pred(..))
import Base.Utils (fst4)

type ClassInfo = ([QualIdent], [(Ident, HasDefaultImpl, IsVisible, Maybe DetScheme)])

type HasDefaultImpl = Bool
type IsVisible      = Bool

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

visibleClassMethods :: QualIdent -> ClassEnv -> [Ident]
visibleClassMethods cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, ms) -> map fst4 $ filter (\(_,_,vis, _) -> vis) ms
  _ -> internalError $ "Env.Classes.visibleClassMethods: " ++ show cls

allClassMethods :: QualIdent -> ClassEnv -> [Ident]
allClassMethods cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, ms) -> map fst4 ms
  _ -> internalError $ "Env.Classes.allClassMethods: " ++ show cls

hasDefaultImpl :: QualIdent -> Ident -> ClassEnv -> Bool
hasDefaultImpl cls f clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, ms) -> case lookup f $ map (\(i, d, _, _) -> (i, d)) ms of
    Just dflt -> dflt
    Nothing -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show f
  _ -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show cls

getDeterminismAnnotation :: QualIdent -> Ident -> ClassEnv -> Maybe DetScheme
getDeterminismAnnotation cls f clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, ms) -> case lookup f $ map (\(i, _, _, d) -> (i, d)) ms of
    Just d -> d
    Nothing -> internalError $ "Env.Classes.getDeterminismAnnotation: " ++ show f
  _ -> internalError $ "Env.Classes.getDeterminismAnnotation: " ++ show cls

-- The function 'minPredSet' transforms a predicate set by removing all
-- predicates from the predicate set which are implied by other predicates
-- according to the super class hierarchy. Inversely, the function 'maxPredSet'
-- adds all predicates to a predicate set which are implied by the predicates
-- in the given predicate set.

minPredSet :: ClassEnv -> PredSet -> PredSet
minPredSet clsEnv ps =
  ps `Set.difference` Set.concatMap implied ps
  where implied (Pred cls ty) = Set.fromList
          [Pred cls' ty | cls' <- tail (allSuperClasses cls clsEnv)]

maxPredSet :: ClassEnv -> PredSet -> PredSet
maxPredSet clsEnv = Set.concatMap implied
  where implied (Pred cls ty) = Set.fromList
          [Pred cls' ty | cls' <- allSuperClasses cls clsEnv]
