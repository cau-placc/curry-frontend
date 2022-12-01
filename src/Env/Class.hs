{- |
    Module      :  $Header$
    Description :  Environment of classes
    Copyright   :  (c) 2016 - 2020 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about all type classes in an
    environment that maps type classes to their arity, a predicate set which
    represents their direct superclasses, a list of tuples of indices that
    represents their functional dependencies and all their associated class 
    methods with an additional flag stating whether an default implementation 
    has been provided or not. For both the type class identifier and the
    predicate set of super classes original names are used. Thus, the use of a
    flat environment is sufficient.
-}

module Env.Class
  ( ClassEnv, initClassEnv
  , ClassInfo, bindClassInfo, mergeClassInfo, lookupClassInfo
  , superClasses, allSuperClasses, classMethods, hasDefaultImpl
  , minPredSet, maxPredSet, genFunDep, cov
  ) where

import           Data.List       (nub, sort)
import qualified Data.Map       as Map (Map, empty, insertWith, lookup)
import qualified Data.Set.Extra as Set (Set, insert, delete, concatMap, isSubsetOf
                                       , union, unions, difference, map, fromList, toList)

import Base.Expr ( Expr (fv) )
import Base.Types
import Base.TypeSubst

import Curry.Base.Ident
import Curry.Syntax.Type
import Curry.Syntax.Pretty (ppIdent)

import Base.Messages (internalError)

-- | The class environment stores the arity of the class, all super classes in
--   form of a predicate set, the functional dependencies and the identifiers
--   of the methods. The boolean value in the method list states whether a
--   method has a default implementation.
type ClassInfo = (Int, PredSet, FunDeps ,[(Ident, Bool)])

-- | The functional dependencies are stored by saving the index of the left
--   and right hand side of a functional dependency
type FunDeps = [([Int],[Int])]

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



funDeps :: QualIdent -> ClassEnv -> FunDeps
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


-- | Taken from Leif-Erik Krueger
minPredSet :: ClassEnv -> PredSet -> PredSet
minPredSet clsEnv ps =
  ps `Set.difference` Set.concatMap (impliedPreds clsEnv) ps

-- | Taken from Leif-Erik Krueger
maxPredSet :: ClassEnv -> PredSet -> PredSet
maxPredSet clsEnv ps = 
  ps `Set.union` Set.concatMap (impliedPreds clsEnv) ps

-- | Taken from Leif-Erik Krueger
impliedPreds :: ClassEnv -> Pred -> PredSet
impliedPreds clsEnv pr@(Pred _ cls tys) = Set.delete (Pred Other cls tys) $
  Set.map (expandAliasType tys) (allSuperClasses cls clsEnv)

-- | Generates a reperesentation of a functional dependency by indexing every
--   type variable with an integer.
genFunDep :: [(Ident,Int)] -> FunDep -> ([Int],[Int])
genFunDep ixs (FunDep _ ltvs rtvs) = 
  (map lookupIndex ltvs, map lookupIndex rtvs)
 where
   lookupIndex ident = case lookup ident ixs of
     Just ix -> ix
     Nothing -> 
       internalError $ "KindCheck.getFunDep: unindexed variable " ++ show (ppIdent ident)

-- | Computes the set of type variables covered by functional dependencies given
--   a context and a set of already covered type variables.
--   The algorithm is taken from Leif-Erik Krueger.
--   The algorithm works as follows (pseudo-code of an imperative language):
--   Input: A context C and a set of already covered type variables V
--   Output: A set of all type varaibles covered by the functional
--   dependencies
--   COV(C,V)
--   V' := V
--   for each C t_1 ... t_m in C do :
--     Consider the declaration class ... => C u_1 ... u_m | F_1, ..., F_n
--     for each l_1 ... l_lmax -> r_1 ... r_rmax in \{ F_1, ... , F_n \} do :
--       if Union \{ TV(t_i) | i in \{ 1, ..., m \} and u_i in \{ l_1, ..., l_lmax } \}
--         is a subset of V :
--            V' := V' union (Union \{ TV(t_i) | i in \{1,...,n\} and u_i in \{r_1,...,r_rmax\}})
--   if V /= V' :
--        V' := COV(C,V')
cov :: Context -> Set.Set Ident -> ClassEnv -> Set.Set Ident
cov cx tvars clsEnv | tvars' == tvars = tvars
                    | otherwise       = cov cx tvars' clsEnv
  where
    tvars' = foldl cov' tvars cx
    
    -- Outer for-loop
    cov' tvs c@(Constraint _ qcls tys) = 
       let fds  = funDeps qcls clsEnv
           itys = zip [1..] (map (Set.fromList . fv) tys)
       in foldl (cov'' itys) tvs fds
    
    -- Inner for-loop
    cov'' itys tvs (lixs,rixs) = 
       let ltvs = Set.unions $ map (lookupVars itys) lixs
           rtvs = Set.unions $ map (lookupVars itys) rixs
       in if   ltvs `Set.isSubsetOf` tvars
          then tvs `Set.union` rtvs
          else tvs
    
    lookupVars itys ix = case lookup ix itys of
      Just itvs -> itvs
      Nothing   -> internalError $ "Env.Class.lookupVars: unbound index " ++ show ix