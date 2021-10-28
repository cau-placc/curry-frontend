{- |
    Module      :  $Header$
    Description :  Environment of classes
    Copyright   :  (c) 2016 - 2020 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about all type classes in an environment
    that maps type classes to their arity, a predicate set representing their
    direct super classes, and all their associated class methods. The latter
    consist of the method name and a flag stating whether an default
    implementation has been provided or not.
    For both the type class identifier and the super class predicates, original
    names are used. Thus, the use of a flat environment is sufficient.
-}

module Env.Class
  ( ClassEnv, initClassEnv
  , ClassInfo, bindClassInfo, mergeClassInfo, lookupClassInfo
  , superClasses, classMethods, hasDefaultImpl, allSuperClasses
  , minPredSet, maxPredSet
  ) where

import qualified Data.Map as Map           (Map, empty, insertWith, lookup)
import qualified Data.Set.Extra as Set     ( Set, concatMap, delete, difference
                                           , insert, map, union )

import Base.Types
import Base.TypeSubst                      (expandAliasType)
import Curry.Base.Ident

import Base.Messages (internalError)

-- -----------------------------------------------------------------------------
-- Type Synonyms
-- -----------------------------------------------------------------------------

-- Type synonyms in super class constraints, which are allowed with the
-- FlexibleContexts extension, are fully expanded when entering a class into the
-- class environment. Type variables in constraints receive indices based on the
-- order of class variables in the declaration head.
-- For example, the context of the class declaration
--   class M.C b a String => D a b
-- is represented by the predicate set {M.C 1 0 [Prelude.Char]} (simplified).

type ClassInfo = (Int, PredSet, [(Ident, Bool)])

type ClassEnv = Map.Map QualIdent ClassInfo

-- -----------------------------------------------------------------------------
-- Environment Building Functions
-- -----------------------------------------------------------------------------

initClassEnv :: ClassEnv
initClassEnv = Map.empty

bindClassInfo :: QualIdent -> ClassInfo -> ClassEnv -> ClassEnv
bindClassInfo cls (arity, sclss, ms) =
  Map.insertWith mergeClassInfo cls (arity, sclss, ms)

-- We have to be careful when merging two class infos into one as hidden class
-- declarations in interfaces provide no information about class methods. If
-- one of the method lists is empty, we simply take the other one. This way,
-- we do overwrite the list of class methods that may have been entered into
-- the class environment before with an empty list.

mergeClassInfo :: ClassInfo -> ClassInfo -> ClassInfo
mergeClassInfo (arity1, sclss1, ms1) (_, _, ms2) =
  (arity1, sclss1, if null ms1 then ms2 else ms1)

-- -----------------------------------------------------------------------------
-- Simple Lookup Functions
-- -----------------------------------------------------------------------------

lookupClassInfo :: QualIdent -> ClassEnv -> Maybe ClassInfo
lookupClassInfo = Map.lookup

-- TODO: Replace 'kindArity' with 'classArity' where possible
classArity :: QualIdent -> ClassEnv -> Int
classArity cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (arity, _, _) -> arity
  _ -> internalError $ "Env.Classes.classArity: " ++ show cls

superClasses :: QualIdent -> ClassEnv -> PredSet
superClasses cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, sclss, _) -> sclss
  _ -> internalError $ "Env.Classes.superClasses: " ++ show cls

classMethods :: QualIdent -> ClassEnv -> [Ident]
classMethods cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, _, ms) -> map fst ms
  _ -> internalError $ "Env.Classes.classMethods: " ++ show cls

hasDefaultImpl :: QualIdent -> Ident -> ClassEnv -> Bool
hasDefaultImpl cls f clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, _, ms) -> case lookup f ms of
    Just dflt -> dflt
    Nothing -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show f
  _ -> internalError $ "Env.Classes.hasDefaultImpl: " ++ show cls

-- -----------------------------------------------------------------------------
-- Super Class Application
-- -----------------------------------------------------------------------------

-- Computes the set of all super class predicates of a class, including the
-- indirect super class predicates and a predicate for the given class itself.
allSuperClasses :: QualIdent -> ClassEnv -> PredSet
allSuperClasses cls clsEnv = allSuperClasses' $
  Pred OPred cls $ map TypeVariable [0 .. classArity cls clsEnv - 1]
 where
  allSuperClasses' pr@(Pred _ scls tys) =
    pr `Set.insert` Set.concatMap (allSuperClasses' . expandAliasType tys)
                                  (superClasses scls clsEnv)

-- The function 'minPredSet' transforms a predicate set by removing all
-- predicates from the predicate set which are implied by other predicates
-- according to the super class hierarchy. Inversely, the function 'maxPredSet'
-- adds all predicates to a predicate set which are implied by the predicates
-- in the given predicate set.

minPredSet :: IsPred a => ClassEnv -> Set.Set a -> Set.Set a
minPredSet clsEnv ps =
  ps `Set.difference` Set.concatMap (impliedPredicates clsEnv) ps

maxPredSet :: IsPred a => ClassEnv -> Set.Set a -> Set.Set a
maxPredSet clsEnv ps =
  ps `Set.union` Set.concatMap (impliedPredicates clsEnv) ps

-- Returns the set of all predicates implied by the given predicate, excluding
-- the given predicate.
impliedPredicates :: IsPred a => ClassEnv -> a -> Set.Set a
impliedPredicates clsEnv pr = Set.delete (getFromPred (Pred OPred cls tys)) $
  Set.map (flip modifyPred pr . const . expandAliasType tys)
          (allSuperClasses cls clsEnv)
  where Pred _ cls tys = getPred pr
