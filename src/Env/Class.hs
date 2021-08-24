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
  , ClassInfo, SuperClassInfo, bindClassInfo, mergeClassInfo
  , constraintToSuperClass, lookupClassInfo, superClasses, classMethods
  , hasDefaultImpl, applySuperClass, allSuperClasses, applyAllSuperClasses
  ) where

import           Data.Containers.ListUtils (nubOrd)
import           Data.List                 (elemIndex, sort)
import qualified Data.Map as Map           (Map, empty, insertWith, lookup)
import           Data.Maybe                (fromMaybe)

import Curry.Base.Ident
import Curry.Syntax.Type (Constraint (Constraint), TypeExpr (VariableType))

import Base.Messages (internalError)

-- TODO: Add and update comments, if this approach works

-- ---------------------------------------------------------------------------
-- Type Synonyms
-- ---------------------------------------------------------------------------

type ClassInfo = (Int, [SuperClassInfo], [(Ident, Bool)])

-- The list represents the type variables of the superclass from left to right.
-- The integers within this list are the indices of these variables in the
-- subclass.
-- examples: class C b => D a b c  -->  (D, [1])
--           class C b a => D a b  -->  (D, [1, 0])
-- Note, that for FlexibleContexts, this has to be (QualIdent, [Type])
type SuperClassInfo = (QualIdent, [Int])

type ClassEnv = Map.Map QualIdent ClassInfo

-- ---------------------------------------------------------------------------
-- Environment Building Functions
-- ---------------------------------------------------------------------------

initClassEnv :: ClassEnv
initClassEnv = Map.empty

bindClassInfo :: QualIdent -> ClassInfo -> ClassEnv -> ClassEnv
bindClassInfo cls (arity, sclss, ms) =
  Map.insertWith mergeClassInfo cls (arity, sort sclss, ms)

-- We have to be careful when merging two class infos into one as hidden class
-- declarations in interfaces provide no information about class methods. If
-- one of the method lists is empty, we simply take the other one. This way,
-- we do overwrite the list of class methods that may have been entered into
-- the class environment before with an empty list.

mergeClassInfo :: ClassInfo -> ClassInfo -> ClassInfo
mergeClassInfo (arity, sclss1, ms1) (_, _, ms2) =
  (arity, sclss1, if null ms1 then ms2 else ms1)

-- Transforms a list of class variables and a super class constraint into super
-- class information.
-- TODO: Check if un-qualification of the class is necessary.
constraintToSuperClass :: [Ident] -> Constraint -> SuperClassInfo
constraintToSuperClass clsvars (Constraint _ cls tys) = (cls, map getIndex tys)
 where
  getIndex :: TypeExpr -> Int
  getIndex (VariableType _ idt) =
    fromMaybe (internalError $ errMsg1 idt) (elemIndex idt clsvars)
  getIndex _                    = internalError errMsg2
  
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
  Just (arity, _, _) -> arity
  _ -> internalError $ "Env.Classes.classArity: " ++ show cls

superClasses :: QualIdent -> ClassEnv -> [SuperClassInfo]
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
