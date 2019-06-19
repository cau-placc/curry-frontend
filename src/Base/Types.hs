{-|
Module      : Base.Types
Description : Internal representation of types
Copyright   : (c) 2002–2004 Wolfgang Lux, Martin Engelke
                  2015 Jan Tikovsky
                  2016 Finn Teegen
                  2019 Jan-Hendrik Matthes
License     : BSD-3-Clause

Maintainer  : fte@informatik.uni-kiel.de
Stability   : experimental
Portability : portable

This module provides the definitions for the internal representation of types in
the compiler along with some helper functions.
-}

-- TODO: Use MultiParamTypeClasses?

module Base.Types
  ( -- * Representation of types
    Type (..)
  , applyType, unapplyType, rootOfType, isArrowType, arrowArity, arrowArgs
  , arrowBase, arrowUnapply
  , typeConstrs, qualifyType, unqualifyType, qualifyTC, weakPrenex
  , IsType (..)
    -- * Representation of predicates and predicate sets
  , Pred (..)
  , qualifyPred, unqualifyPred
  , PredSet
  , emptyPredSet, partitionPredSet, minPredSet, maxPredSet, qualifyPredSet
  , unqualifyPredSet
  , predType, unpredType
    -- * Representation of data constructors
  , DataConstr (..)
  , constrIdent, constrTypes, recLabels, recLabelTypes, tupleData
    -- * Representation of class methods
  , ClassMethod (..)
  , methodName, methodArity, methodType
    -- * Representation of quantification
  , monoType, polyType, typeScheme, rawType, rawPredType
    -- * Predefined types
  , arrowType, unitType, predUnitType, boolType, predBoolType, charType
  , intType, predIntType, floatType, predFloatType, stringType, predStringType
  , listType, consType, ioType, tupleType
  , numTypes, fractionalTypes, predefTypes
  ) where

import qualified Data.Set.Extra   as Set

import           Curry.Base.Ident

import           Base.Messages    (internalError)
import           Env.Class        (ClassEnv, allSuperClasses)

-- -----------------------------------------------------------------------------
-- Types
-- -----------------------------------------------------------------------------

-- | A type is either a type constructor, a type variable, an application
-- of a type to another type, an arrow type, a type with type constraints, or
-- a universal quantified type. An arrow type could be expressed by using
-- 'TypeApply' with the function type constructor, but we currently use
-- 'TypeArrow' because arrow types are used so frequently.
--
-- The 'TypeConstrained' constructor is used for representing type variables
-- that are restricted to a particular set of types. At present, this is used
-- for typing integer literals, which are restricted to types 'Int' and
-- 'Float'. If the type is not restricted, it defaults to the first type
-- from the constraint list.
--
-- Type variables are represented with /de Bruijn style/ indices. Universally
-- quantified type variables are assigned indices in the order of their
-- occurrence in the type from left to right. This leads to a canonical
-- representation of types where alpha-equivalence of two types coincides with
-- equality of the representation.
--
-- Note that even though 'TypeConstrained' variables use indices as well, these
-- variables must never be quantified.
--
-- Note further that the order of constructors is important for the derived
-- 'Ord' instance. In particular, it is essential that a type variable is
-- considered less than a type application (see predicates and predicate sets
-- below for more information).
data Type = TypeConstructor QualIdent
          | TypeVariable Int
          | TypeConstrained [Type] Int
          | TypeApply Type Type
          | TypeArrow Type Type
          | TypeContext PredSet Type
          | TypeForall [Int] Type
  deriving (Eq, Ord, Show)

-- | Applies a type to a list of argument types, whereas applications of the
-- function type constructor to two arguments are converted into an arrow type.
applyType :: Type -> [Type] -> Type
applyType (TypeConstructor tc) [ty1, ty2]
  | tc == qArrowId = TypeArrow ty1 ty2
applyType (TypeApply (TypeConstructor tc) ty) [ty']
  | tc == qArrowId = TypeArrow ty ty'
applyType ty tys = foldl TypeApply ty tys

-- | Decomposes a type into a root type and a list of argument types.
unapplyType :: Bool -> Type -> (Type, [Type])
unapplyType dflt = unapply []
  where
    unapply tys (TypeConstrained tys' tv)
      | dflt                              = unapply tys (head tys')
      | otherwise                         = (TypeConstrained tys' tv, tys)
    unapply tys (TypeApply ty1 ty2)       = unapply (ty2:tys) ty1
    unapply tys (TypeArrow ty1 ty2)
      = (TypeConstructor qArrowId, ty1:ty2:tys)
    unapply tys ty                        = (ty, tys)

-- | Returns the name of the type constructor at the root of a type.
rootOfType :: Type -> QualIdent
rootOfType ty = case fst (unapplyType True ty) of
  TypeConstructor tc -> tc
  _                  -> internalError $ "Base.Types.rootOfType: " ++ show ty

-- | Checks whether a type is a function type.
isArrowType :: Type -> Bool
isArrowType (TypeArrow _ _) = True
isArrowType _               = False

-- | Returns the arity of a function type.
arrowArity :: Type -> Int
arrowArity = length . arrowArgs

-- | Returns the argument types of a function type.
arrowArgs :: Type -> [Type]
arrowArgs = fst . arrowUnapply

-- | Returns the result type of a function type.
arrowBase :: Type -> Type
arrowBase = snd . arrowUnapply

-- | Returns the argument types and the result type of a function type.
arrowUnapply :: Type -> ([Type], Type)
arrowUnapply (TypeArrow ty1 ty2) = let (tys, ty) = arrowUnapply ty2
                                    in (ty1:tys, ty)
arrowUnapply ty                  = ([], ty)

-- | Returns a list of all type constructors occuring in a type.
typeConstrs :: Type -> [QualIdent]
typeConstrs = constrs []
  where
    constrs tcs (TypeConstructor tc) = tc:tcs
    constrs tcs (TypeApply ty1 ty2)  = constrs (constrs tcs ty2) ty1
    constrs tcs (TypeArrow ty1 ty2)  = constrs (constrs tcs ty2) ty1
    constrs tcs (TypeContext _ ty)   = constrs tcs ty
    constrs tcs (TypeForall _ ty)    = constrs tcs ty
    constrs tcs _                    = tcs

-- | Adds the qualification with a module identifier to every type constructor
-- in a type.
qualifyType :: ModuleIdent -> Type -> Type
qualifyType m (TypeConstructor tc)     = TypeConstructor (qualifyTC m tc)
qualifyType _ tv@(TypeVariable _)      = tv
qualifyType m (TypeConstrained tys tv)
  = TypeConstrained (map (qualifyType m) tys) tv
qualifyType m (TypeApply ty1 ty2)
  = TypeApply (qualifyType m ty1) (qualifyType m ty2)
qualifyType m (TypeArrow ty1 ty2)
  = TypeArrow (qualifyType m ty1) (qualifyType m ty2)
qualifyType m (TypeContext ps ty)
  = TypeContext (qualifyPredSet m ps) (qualifyType m ty)
qualifyType m (TypeForall tvs ty)      = TypeForall tvs (qualifyType m ty)

-- | Removes the qualification with a module identifier from every type
-- constructor in a type.
unqualifyType :: ModuleIdent -> Type -> Type
unqualifyType m (TypeConstructor tc)     = TypeConstructor (qualUnqualify m tc)
unqualifyType _ tv@(TypeVariable _)      = tv
unqualifyType m (TypeConstrained tys tv)
  = TypeConstrained (map (unqualifyType m) tys) tv
unqualifyType m (TypeApply ty1 ty2)
  = TypeApply (unqualifyType m ty1) (unqualifyType m ty2)
unqualifyType m (TypeArrow ty1 ty2)
  = TypeArrow (unqualifyType m ty1) (unqualifyType m ty2)
unqualifyType m (TypeContext ps ty)
  = TypeContext (unqualifyPredSet m ps) (unqualifyType m ty)
unqualifyType m (TypeForall tvs ty)      = TypeForall tvs (unqualifyType m ty)

-- | Qualifies the type constructor with the given module identifier if it is
-- not a type constructor of a primitive type.
qualifyTC :: ModuleIdent -> QualIdent -> QualIdent
qualifyTC m tc | isPrimTypeId tc = tc
               | otherwise       = qualQualify m tc

-- | Converts the given type into weak-prenex form.
weakPrenex :: Type -> Type
weakPrenex ty@(TypeArrow ty1 ty2)  = case weakPrenex ty2 of
  TypeForall tvs ty2' -> TypeForall tvs (TypeArrow ty1 ty2')
  _                   -> ty
weakPrenex ty@(TypeForall tvs ty1) = case weakPrenex ty1 of
  TypeForall tvs' ty1' -> TypeForall (tvs ++ tvs') ty1'
  _                    -> ty
weakPrenex ty                      = ty

class IsType t where
  -- | Returns a list of all non universally quantified type variables occurring
  -- in a type. Note that 'TypeConstrained' variables are not included in the
  -- set of type variables because they cannot be generalized.
  typeVars :: t -> [Int]

instance IsType Type where
  typeVars = vars []
    where
      vars tvs (TypeVariable tv)    = tv:tvs
      vars tvs (TypeApply ty1 ty2)  = vars (vars tvs ty2) ty1
      vars tvs (TypeArrow ty1 ty2)  = vars (vars tvs ty2) ty1
      vars tvs (TypeContext ps ty)  = typeVars ty ++ typeVars ps ++ tvs
      vars tvs (TypeForall tvs' ty)
        = filter (`notElem` tvs') (typeVars ty) ++ tvs
      vars tvs _                    = tvs

-- -----------------------------------------------------------------------------
-- Predicates
-- -----------------------------------------------------------------------------

-- | A predicate consists of a type class identifier and a type.
data Pred = Pred QualIdent Type
  deriving (Eq, Show)

-- We provide a custom 'Ord' instance for predicates here where we consider the
-- type component of the predicate before the class component (see predicate
-- sets below for more information).
instance Ord Pred where
  Pred cls1 ty1 `compare` Pred cls2 ty2 = case ty1 `compare` ty2 of
    LT -> LT
    EQ -> cls1 `compare` cls2
    GT -> GT

instance IsType Pred where
  typeVars (Pred _ ty) = typeVars ty

-- | Adds the qualification with a module identifier to a predicate.
qualifyPred :: ModuleIdent -> Pred -> Pred
qualifyPred m (Pred cls ty) = Pred (qualQualify m cls) (qualifyType m ty)

-- | Removes the qualification with a module identifier from a predicate.
unqualifyPred :: ModuleIdent -> Pred -> Pred
unqualifyPred m (Pred cls ty) = Pred (qualUnqualify m cls) (unqualifyType m ty)

-- -----------------------------------------------------------------------------
-- Predicate sets
-- -----------------------------------------------------------------------------

-- | A predicate set is an ordered set of predicates. This way, we do not have
-- to manually take care of duplicate predicates and have automatically achieved
-- a canonical representation (as only original names for type classes are
-- used). Having the order on types and predicates in mind, we have also ensured
-- that a class method's implicit class constraint is always the minimum element
-- of a method's predicate set, thus making it very easy to remove it.
type PredSet = Set.Set Pred

instance (IsType a, Ord a) => IsType (Set.Set a) where
  typeVars = concat . Set.toList . Set.map typeVars

-- | The empty predicate set.
emptyPredSet :: PredSet
emptyPredSet = Set.empty

-- | Partitions the predicates in a predicate set into two predicate sets. The
-- first predicate set contains all predicates that contain only type variables.
partitionPredSet :: PredSet -> (PredSet, PredSet)
partitionPredSet = Set.partition (\(Pred _ ty) -> isTypeVariable ty)
  where
    isTypeVariable (TypeVariable _) = True
    isTypeVariable (TypeApply ty _) = isTypeVariable ty
    isTypeVariable _                = False

-- | Transforms a predicate set by removing all predicates which are implied by
-- other predicates according to the super class hierarchy.
minPredSet :: ClassEnv -> PredSet -> PredSet
minPredSet clsEnv ps = ps `Set.difference` Set.concatMap implied ps
  where
    implied (Pred cls ty) = Set.fromList
      [Pred cls' ty | cls' <- tail (allSuperClasses cls clsEnv)]

-- | Transforms a predicate set by adding all predicates which are implied by
-- other predicates according to the super class hierarchy.
maxPredSet :: ClassEnv -> PredSet -> PredSet
maxPredSet clsEnv = Set.concatMap implied
  where
    implied (Pred cls ty) = Set.fromList
      [Pred cls' ty | cls' <- allSuperClasses cls clsEnv]

-- | Adds the qualification with a module identifier to a predicate set.
qualifyPredSet :: ModuleIdent -> PredSet -> PredSet
qualifyPredSet m = Set.map (qualifyPred m)

-- | Removes the qualification with a module identifier from a predicate set.
unqualifyPredSet :: ModuleIdent -> PredSet -> PredSet
unqualifyPredSet m = Set.map (unqualifyPred m)

-- -----------------------------------------------------------------------------
-- Predicated types
-- -----------------------------------------------------------------------------

-- | Transforms a type into a predicated type with an empty predicate set.
predType :: Type -> Type
predType = TypeContext emptyPredSet

-- | Removes the predicate set from a predicated type.
unpredType :: Type -> Type
unpredType (TypeContext _ ty) = ty
unpredType ty                 = ty

-- -----------------------------------------------------------------------------
-- Data constructors
-- -----------------------------------------------------------------------------

-- | Represents value or record constructors introduced by data or newtype
-- declarations.
data DataConstr = DataConstr Ident [Type]
                | RecordConstr Ident [Ident] [Type]
  deriving (Eq, Show)

-- | Returns the identifier of a data constructor.
constrIdent :: DataConstr -> Ident
constrIdent (DataConstr c _)     = c
constrIdent (RecordConstr c _ _) = c

-- | Returns the argument types of a data constructor.
constrTypes :: DataConstr -> [Type]
constrTypes (DataConstr _ tys)     = tys
constrTypes (RecordConstr _ _ tys) = tys

-- | Returns the record label identifiers of a data constructor.
recLabels :: DataConstr -> [Ident]
recLabels (DataConstr _ _)      = []
recLabels (RecordConstr _ ls _) = ls

-- | Returns the record label types of a data constructor.
recLabelTypes :: DataConstr -> [Type]
recLabelTypes (DataConstr _ _)       = []
recLabelTypes (RecordConstr _ _ tys) = tys

-- | Returns the data constructors for tuples.
tupleData :: [DataConstr]
tupleData = [DataConstr (tupleId n) (take n tvs) | n <- [2..]]
  where
    tvs = map TypeVariable [0..]

-- -----------------------------------------------------------------------------
-- Class methods
-- -----------------------------------------------------------------------------

-- | Represents class methods introduced by class declarations. The 'Maybe Int'
-- argument denotes the arity of the provided default implementation.
data ClassMethod = ClassMethod Ident (Maybe Int) Type
  deriving (Eq, Show)

-- | Returns the identifier of a class method.
methodName :: ClassMethod -> Ident
methodName (ClassMethod f _ _) = f

-- | Returns the arity of a class method.
methodArity :: ClassMethod -> Maybe Int
methodArity (ClassMethod _ a _) = a

-- | Returns the type of a class method.
methodType :: ClassMethod -> Type
methodType (ClassMethod _ _ ty) = ty

-- -----------------------------------------------------------------------------
-- Quantification
-- -----------------------------------------------------------------------------

-- | Translates a type into a monomorphic type scheme.
monoType :: Type -> Type
monoType = TypeForall [] . predType

-- | Translates a type into a polymorphic type scheme. It assumes that all
-- universally quantified type variables in the type are assigned indices
-- starting with 0 and does not renumber the variables.
polyType :: Type -> Type
polyType = typeScheme . predType

-- | Translates a type into a type scheme.
typeScheme :: Type -> Type
typeScheme ty = TypeForall (typeVars ty) ty

-- | Strips the quantifier and predicate set from a type scheme.
rawType :: Type -> Type
rawType (TypeForall _ (TypeContext _ ty)) = ty
rawType ty                                = rawPredType ty

-- | Strips the quantifier from a type scheme.
rawPredType :: Type -> Type
rawPredType (TypeForall _ ty) = ty
rawPredType ty                = ty

-- -----------------------------------------------------------------------------
-- Predefined types
-- -----------------------------------------------------------------------------

-- | Returns a primitive type from an identifier and a list of argument types.
primType :: QualIdent -> [Type] -> Type
primType = applyType . TypeConstructor

-- | Returns an arrow type from two types.
arrowType :: Type -> Type -> Type
arrowType ty1 ty2 = primType qArrowId [ty1, ty2]

-- | Returns the unit type.
unitType :: Type
unitType = primType qUnitId []

-- | Returns the predicated unit type.
predUnitType :: Type
predUnitType = predType unitType

-- | Returns the bool type.
boolType :: Type
boolType = primType qBoolId []

-- | Returns the predicated bool type.
predBoolType :: Type
predBoolType = predType boolType

-- | Returns the char type.
charType :: Type
charType = primType qCharId []

-- | Returns the integer type.
intType :: Type
intType = primType qIntId []

-- | Returns the predicated integer type.
predIntType :: Type
predIntType = predType intType

-- | Returns the float type.
floatType :: Type
floatType = primType qFloatId []

-- | Returns the predicated float type.
predFloatType :: Type
predFloatType = predType floatType

-- | Returns the string type.
stringType :: Type
stringType = listType charType

-- | Returns the predicated string type.
predStringType :: Type
predStringType = predType stringType

-- | Returns a list type with the given argument type.
listType :: Type -> Type
listType ty = primType qListId [ty]

-- | Returns a type of the form @ty -> [ty] -> [ty]@ for a type @ty@.
consType :: Type -> Type
consType ty = TypeArrow ty (TypeArrow (listType ty) (listType ty))

-- | Returns an IO type with the given argument type.
ioType :: Type -> Type
ioType ty = primType qIOId [ty]

-- | Returns a tuple type with the given list of argument types.
tupleType :: [Type] -> Type
tupleType tys = primType (qTupleId (length tys)) tys

-- | The list of numerical types for numeric literals in patterns.
numTypes :: [Type]
numTypes = [intType, floatType]

-- | The list of fractional types for numeric literals in patterns.
fractionalTypes :: [Type]
fractionalTypes = drop 1 numTypes

-- | The list of predefined types with its corresponding data constructors.
predefTypes :: [(Type, [DataConstr])]
predefTypes = [ (arrowType a b, [])
              , (unitType, [DataConstr unitId []])
              , (listType a, [ DataConstr nilId []
                             , DataConstr consId [a, listType a] ]) ]
  where
    a = TypeVariable 0
    b = TypeVariable 1
