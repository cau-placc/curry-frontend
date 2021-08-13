{- |
    Module      :  $Header$
    Description :  Environment of classes
    Copyright   :  (c) 2016 - 2020 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about all type classes in an environment
    that maps type classes to their arity, a sorted list of their direct super
    classes, their functional dependencies, and all their associated class
    methods with an additional flag stating whether an default implementation
    has been provided or not. For both the type class identifier and the list of
    super classes original names are used. Thus, the use of a flat environment
    is sufficient.
-}

module Env.Class
  ( ClassEnv, initClassEnv
  , ClassInfo, SuperClassInfo, FunDep, bindClassInfo, mergeClassInfo
  , constraintToSuperClass, lookupClassInfo, superClasses, classFunDeps
  , classMethods, hasDefaultImpl, applySuperClass, allSuperClasses
  , applyAllSuperClasses, toFunDep, fromFunDep, funDepCoverage
  ) where

import           Data.Containers.ListUtils (nubOrd)
import           Data.List                 (elemIndex, partition, sort)
import qualified Data.Map as Map           (Map, empty, insertWith, lookup)
import           Data.Maybe                (fromMaybe, mapMaybe)
import qualified Data.Set as Set           ( Set, fromList, isSubsetOf, unions
                                           , size, toList )

import           Curry.Base.Ident
import           Curry.Base.SpanInfo
import qualified Curry.Syntax.Type as CS

import Base.Messages (internalError)

-- TODO: Add and update comments, if this approach works

-- ---------------------------------------------------------------------------
-- Type Synonyms
-- ---------------------------------------------------------------------------

type ClassInfo = (Int, [SuperClassInfo], [FunDep], [(Ident, Bool)])

-- The list represents the type variables of the superclass from left to right.
-- The integers within this list are the indices of these variables in the
-- subclass.
-- examples: class C b => D a b c  -->  (D, [1])
--           class C b a => D a b  -->  (D, [1, 0])
-- Note, that for FlexibleContexts, this has to be (QualIdent, [Type])
type SuperClassInfo = (QualIdent, [Int])

-- In the class environment, functional dependencies are represented by a pair
-- of sets containing the indices of the type variables on the left and right
-- hand side of the functional dependency respectively.
type FunDep = (Set.Set Int, Set.Set Int)

type ClassEnv = Map.Map QualIdent ClassInfo

-- ---------------------------------------------------------------------------
-- Environment Building Functions
-- ---------------------------------------------------------------------------

initClassEnv :: ClassEnv
initClassEnv = Map.empty

bindClassInfo :: QualIdent -> ClassInfo -> ClassEnv -> ClassEnv
bindClassInfo cls (arity, sclss, funDeps, ms) =
  Map.insertWith mergeClassInfo cls (arity, sort sclss, sort funDeps, ms)

-- We have to be careful when merging two class infos into one as hidden class
-- declarations in interfaces provide no information about class methods. If
-- one of the method lists is empty, we simply take the other one. This way,
-- we do overwrite the list of class methods that may have been entered into
-- the class environment before with an empty list.

mergeClassInfo :: ClassInfo -> ClassInfo -> ClassInfo
mergeClassInfo (arity, sclss, funDeps, ms1) (_, _, _, ms2) =
  (arity, sclss, funDeps, if null ms1 then ms2 else ms1)

-- Transforms a list of class variables and a super class constraint into super
-- class information.
-- TODO: Check if un-qualification of the class is necessary.
constraintToSuperClass :: [Ident] -> CS.Constraint -> SuperClassInfo
constraintToSuperClass clsvars (CS.Constraint _ cls tys) =
  (cls, map getIndex tys)
 where
  getIndex :: CS.TypeExpr -> Int
  getIndex (CS.VariableType _ idt) =
    fromMaybe (internalError $ errMsg1 idt) (elemIndex idt clsvars)
  getIndex _                       = internalError errMsg2
  
  errMsgLoc   = "Env.Classes.constraintToSuperClass: "
  errMsg1 idt = errMsgLoc ++ "Variable " ++ show idt ++
                " missing in class variables of " ++ show cls
  errMsg2     = errMsgLoc ++ "Non-variable type in context of " ++ show cls

-- ---------------------------------------------------------------------------
-- Simple Lookup Functions
-- ---------------------------------------------------------------------------

lookupClassInfo :: QualIdent -> ClassEnv -> Maybe ClassInfo
lookupClassInfo = Map.lookup

classArity :: QualIdent -> ClassEnv -> Int
classArity cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (arity, _, _, _) -> arity
  _ -> internalError $ "Env.Classes.classArity: " ++ show cls

superClasses :: QualIdent -> ClassEnv -> [SuperClassInfo]
superClasses cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, sclss, _, _) -> sclss
  _ -> internalError $ "Env.Classes.superClasses: " ++ show cls

classFunDeps :: QualIdent -> ClassEnv -> [FunDep]
classFunDeps cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, _, funDeps, _) -> funDeps
  _ -> internalError $ "Env.Classes.classFunDeps: " ++ show cls

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

-- ---------------------------------------------------------------------------
-- Super Class Application
-- ---------------------------------------------------------------------------

applySuperClass :: [a] -> SuperClassInfo -> (QualIdent, [a])
applySuperClass tys (scls, varIs) = (scls, reorderTypes varIs)
 where
  -- reorderTypes :: [Int] -> [a]
  reorderTypes []                   = []
  reorderTypes (nextVarIx : remVIs) = tys `at` nextVarIx : reorderTypes remVIs

  -- Like (!!), but with a different error message.
  at :: [a] -> Int -> a
  at (x : _ ) 0         = x
  at (_ : xs) n | n > 0 = xs `at` (n - 1)
  at _        _         =
    internalError $ "Env.Classes.applySuperClass: " ++ show scls

allSuperClasses :: QualIdent -> ClassEnv -> [SuperClassInfo]
allSuperClasses cls clsEnv =
  nubOrd $ allSuperClasses' (cls, [0 .. classArity cls clsEnv - 1])
 where
  allSuperClasses' sclsInfo@(scls, varIs) =
    sclsInfo : concatMap (allSuperClasses' . applySuperClass varIs)
                         (superClasses scls clsEnv)

applyAllSuperClasses :: QualIdent -> [a] -> ClassEnv -> [(QualIdent, [a])]
applyAllSuperClasses cls tys clsEnv =
  map (applySuperClass tys) (allSuperClasses cls clsEnv)

-- ---------------------------------------------------------------------------
-- Functional Dependencies
-- ---------------------------------------------------------------------------

-- 'toFunDep' and 'fromFunDep' convert functional dependencies between the
-- formats of the AST and the class environment. A list of the type variables of
-- the respective class is needed for both conversion directions.

toFunDep :: [Ident] -> CS.FunDep -> FunDep
toFunDep clsvars (CS.FunDep _ ltvs rtvs) =
  (Set.fromList (map getIndex ltvs), Set.fromList (map getIndex rtvs))
 where
  getIndex :: Ident -> Int
  getIndex idt = fromMaybe (internalError $ errMsg idt) $ elemIndex idt clsvars

  errMsg idt = "Env.Classes.toFunDep: Variable " ++ show idt ++
                " missing in class variables " ++ show clsvars

fromFunDep :: [Ident] -> FunDep -> CS.FunDep
fromFunDep clsvars (lset, rset) =
  CS.FunDep NoSpanInfo (toIdents lset) (toIdents rset)
 where
  toIdents :: Set.Set Int -> [Ident]
  toIdents = map (clsvars `at`) . Set.toList
  
  -- Like (!!), but with a different error message.
  at :: [a] -> Int -> a
  at (x : _ ) 0         = x
  at (_ : xs) n | n > 0 = xs `at` (n - 1)
  at _        _         =
    internalError $ "Env.Classes.fromFunDep: " ++ show (clsvars, (lset, rset))

-- 'funDepCoverage' takes a complete and correctly ordered list of arguments
-- applied to a type class, for example all class variables, the functional
-- dependencies of that class, and a list containing a subset of the type class
-- arguments and returns the list containing all type class arguments that are
-- uniquely determined by the given subset according to the functional
-- dependencies.

funDepCoverage :: (Ord a, Show a) => [a] -> [FunDep] -> [a] -> [a]
funDepCoverage fullCov funDeps cov =
  let covSet0 = Set.fromList $ mapMaybe (`elemIndex` fullCov) cov
  in nubOrd $ cov ++ (map (fullCov `at`) $
                          Set.toList $ funDepCoverage' funDeps covSet0)
 where
  funDepCoverage' :: [FunDep] -> Set.Set Int -> Set.Set Int
  funDepCoverage' fds covSet =
    let (useFds, oFds) = partition ((`Set.isSubsetOf` covSet) . fst) fds
        covSet' = Set.unions $ covSet : (map snd useFds)
    in if Set.size covSet == Set.size covSet' then covSet
                                              else funDepCoverage' oFds covSet'

  -- Like (!!), but with a different error message.
  at :: [a] -> Int -> a
  at (x : _ ) 0         = x
  at (_ : xs) n | n > 0 = xs `at` (n - 1)
  at _        _         =
    internalError $ "Env.Classes.funDepCoverage: " ++ show (fullCov, funDeps)
