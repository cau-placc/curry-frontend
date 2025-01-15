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
    methods with additional flags stating 
      a) whether an default implementation has been provided or not.
      b) whether the method is visible.
    For both the type class identifier and the list of
    super classes original names are used. Thus, the use of a flat environment
    is sufficient.
-}

module Curry.Frontend.Env.Class
  ( ClassEnv, initClassEnv
  , ClassInfo, SuperClassInfo, FunDep, bindClassInfo, mergeClassInfo
  , constraintToSuperClass, lookupClassInfo, superClasses, classFunDeps
  , classMethods, hasDefaultImpl, isVisibleMethod, applySuperClass, allSuperClasses
  , toFunDep, fromFunDep, getFunDepLhs, getFunDepRhs
  , deleteVarFunDep, renameVarFunDep, renameFunDep, removeTrivialFunDeps
  , getRhsOnLhsMatch, funDepCoverage, funDepCoveragePredList, ambiguousTypeVars
  , minPredList, maxPredList, impliedPredicatesList, toFunDepMap
  ) where

import           Data.Containers.ListUtils (nubOrd)
import           Data.List                 (elemIndex, nub, partition, sort)
import qualified Data.Map as Map           ( Map, empty, insertWith, lookup
                                           , map )
import           Data.Maybe                (fromMaybe)
import qualified Data.Set as Set           ( Set, delete, difference, findMax
                                           , fromList, insert, isSubsetOf
                                           , lookupMax, map, member, notMember
                                           , null, singleton, size, toList
                                           , union, unions )

import           Curry.Frontend.Base.Types
import           Curry.Frontend.Base.TypeSubst (expandAliasType)

import           Curry.Base.Ident
import           Curry.Base.SpanInfo
import qualified Curry.Syntax.Type as CS

import Curry.Frontend.Base.Messages (internalError)

-- ---------------------------------------------------------------------------
-- Type Synonyms
-- ---------------------------------------------------------------------------

type Flags = (Bool, Bool)

type ClassInfo = (Int, [Pred], [FunDep], [(Ident, Flags)])

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

superClasses :: QualIdent -> ClassEnv -> [Pred]
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

flags :: QualIdent -> Ident -> ClassEnv -> Flags
flags cls f clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, _, _, ms) -> case lookup f ms of
    Just dflt -> dflt
    Nothing -> internalError $ "Env.Classes.flags: " ++ show f
  _ -> internalError $ "Env.Classes.flags: " ++ show cls

hasDefaultImpl :: QualIdent -> Ident -> ClassEnv -> Bool
hasDefaultImpl cls f clsEnv = fst $ flags cls f clsEnv

isVisibleMethod :: QualIdent -> Ident -> ClassEnv -> Bool
isVisibleMethod cls f clsEnv = snd $ flags cls f clsEnv

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

-- taken from Leif-Erik Krueger
-- Computes the set of all super class predicates of a class, including the
-- indirect super class predicates and a predicate for the given class itself.
allSuperClasses :: QualIdent -> ClassEnv -> [Pred]
allSuperClasses cls clsEnv = allSuperClasses' $
  Pred OPred cls $ map TypeVariable [0 .. classArity cls clsEnv - 1]
 where
  allSuperClasses' pr@(Pred _ scls tys) =
    pr `plInsert` plConcatMap (allSuperClasses' . expandAliasType tys)
                                  (superClasses scls clsEnv)

-- The function 'minPredSet' transforms a predicate set by removing all
-- predicates from the predicate set which are implied by other predicates
-- according to the super class hierarchy. Inversely, the function 'maxPredSet'
-- adds all predicates to a predicate set which are implied by the predicates
-- in the given predicate set.

-- List version of minPredList
minPredList :: IsPred a => ClassEnv -> [a] -> [a]
minPredList clsEnv pls =
  plDifference pls (plConcatMap (impliedPredicatesList clsEnv) pls)

-- List version of maxPredSet
maxPredList :: IsPred a => ClassEnv -> [a] -> [a]
maxPredList clsEnv pls =
  plUnion pls (concatMap (impliedPredicatesList clsEnv) pls)

impliedPredicatesList :: IsPred a => ClassEnv -> a -> [a]
impliedPredicatesList clsEnv pr = plDelete (getFromPred (Pred OPred cls tys)) $
  nub $ map (flip modifyPred pr . const . expandAliasType tys)
            (allSuperClasses cls clsEnv)
  where Pred _ cls tys = getPred pr

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

getFunDepLhs :: Show a => FunDep -> [a] -> [a]
getFunDepLhs (lhsSet, _) ls = getFunDepLhs' 0 ls
 where
  maxIndex = fromMaybe (-1) (Set.lookupMax lhsSet)

  getFunDepLhs' :: Show a => Int -> [a] -> [a]
  getFunDepLhs' i _      | i > maxIndex          = []
  getFunDepLhs' i (x:xs) | i `Set.member` lhsSet = x : getFunDepLhs' (i + 1) xs
                         | otherwise             =     getFunDepLhs' (i + 1) xs
  getFunDepLhs' _ [] = internalError $ "Env.Classes.getFunDepLhs: Maximum " ++
    "fundep index " ++ show maxIndex ++ " exceeds length of list " ++ show ls

getFunDepRhs :: Show a => FunDep -> [a] -> [a]
getFunDepRhs (lhsSet, rhsSet) = getFunDepLhs (rhsSet, lhsSet)

deleteVarFunDep :: Int -> FunDep -> FunDep
deleteVarFunDep tv (lhsSet, rhsSet) =
  (Set.delete tv lhsSet, Set.delete tv rhsSet)

renameVarFunDep :: Int -> Int -> FunDep -> FunDep
renameVarFunDep tv tv' (lhsSet, rhsSet) =
  let rename set = if Set.member tv set then Set.insert tv' (Set.delete tv set)
                                        else set
  in (rename lhsSet, rename rhsSet)

renameFunDep :: Int -> FunDep -> FunDep
renameFunDep n (lhsSet, rhsSet) = (Set.map (+ n) lhsSet, Set.map (+ n) rhsSet)

removeTrivialFunDeps :: [FunDep] -> [FunDep]
removeTrivialFunDeps = nubOrd . filter (not . Set.null . snd) .
  map (\(lhsSet, rhsSet) -> (lhsSet, rhsSet `Set.difference` lhsSet))

getRhsOnLhsMatch :: (Eq a, Show a) => FunDep -> [a] -> [a] -> Maybe ([a], [a])
getRhsOnLhsMatch funDep xs ys =
  if getFunDepLhs funDep xs == getFunDepLhs funDep ys
    then Just (getFunDepRhs funDep xs, getFunDepRhs funDep ys)
    else Nothing

-- 'funDepCoverage' calculates the set of all type variables that are uniquely
-- determined by the given set of type variables by recursively applying the
-- given list of functional dependencies.

funDepCoverage :: [FunDep] -> Set.Set Int -> Set.Set Int
funDepCoverage fds covSet =
  let (useFds, oFds) = partition ((`Set.isSubsetOf` covSet) . fst) fds
      covSet' = Set.unions $ covSet : map snd useFds
  in if Set.size covSet == Set.size covSet' then covSet
                                            else funDepCoverage oFds covSet'

funDepCoveragePredList :: IsPred a => ClassEnv -> [a] -> Set.Set Int
                                  -> Set.Set Int
funDepCoveragePredList clsEnv pls tvSet =
  let predList = map getPred pls
      tvSetPs = Set.fromList (typeVars predList)
      freshVar = Set.findMax (Set.insert (-1) (tvSet `Set.union` tvSetPs)) + 1
      funDeps = removeTrivialFunDeps $ predListFunDeps freshVar predList
  in funDepCoverage funDeps tvSet
 where
  predListFunDeps :: Int -> [Pred] -> [FunDep]
  predListFunDeps _ [] = []
  predListFunDeps freshVar (Pred _ cls tys : preds) =
    let (freshVar', funDeps) = instantiateFunDeps tys freshVar $
          map (renameFunDep freshVar) $ classFunDeps cls clsEnv
    in funDeps ++ predListFunDeps freshVar' preds

  instantiateFunDeps :: [Type] -> Int -> [FunDep] -> (Int, [FunDep])
  instantiateFunDeps [] i funDeps = (i, funDeps)
  instantiateFunDeps (ty : tys) i funDeps = instantiateFunDeps tys (i + 1) $
    case nub (typeVars ty) of
      []   -> map (deleteVarFunDep i) funDeps
      [tv] -> map (renameVarFunDep i tv) funDeps
      tvs  -> let (tvs', freshVar) = (Set.fromList tvs, Set.singleton i)
              in (tvs', freshVar) : (freshVar, tvs') : funDeps


ambiguousTypeVars :: ClassEnv -> PredType -> Set.Set Int -> [Int]
ambiguousTypeVars clsEnv (PredType pls ty) fvs =
  let coveredVars = funDepCoveragePredList clsEnv pls $
                      Set.fromList (typeVars ty) `Set.union` fvs
  in filter (`Set.notMember` coveredVars) (typeVars pls)


-------------------------------------------------------------------------------
-- Conversion to simplified class environment for Type Syntax Check
-------------------------------------------------------------------------------


toFunDepMap :: ClassEnv -> Map.Map QualIdent [FunDep]
toFunDepMap = Map.map (\(_,_,fds,_) -> fds)
