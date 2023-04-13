{- |
    Module      :  $Header$
    Description :  Internal representation of types
    Copyright   :  (c) 2002 - 2004 Wolfgang Lux
                                   Martin Engelke
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module modules provides the definitions for the internal
   representation of types in the compiler along with some helper functions.
-}

-- TODO: Use MultiParamTypeClasses ?

module Base.Types
  ( -- * Representation of types
    Type (..), applyType, unapplyType, rootOfType
  , isTypeVariable, isAppliedTypeVariable
  , isArrowType, arrowArity, arrowArgs, arrowBase, arrowUnapply
  , IsType (..), typeConstrs, removeTypeConstrained
  , qualifyType, unqualifyType, qualifyTC
    -- * Representation of predicates, predicate sets and predicated types
  , Pred (..), PredIsICC (..), IsPred (..), LPred (..), qualifyPred
  , unqualifyPred
  , PredSet, emptyPredSet, LPredSet, emptyLPredSet, psMember, removeICCFlag
  , qualifyPredSet, unqualifyPredSet
  , PredList, LPredList, plElem, removeICCFlagList, partitionPredList
  , qualifyPredList, unqualifyPredList
  , plUnion, plUnions, plDeleteMin, plDelete, plConcatMap
  , plConcatMapM, plInsert, plDifference, plLookupMin
  , PredType (..), predType, unpredType, qualifyPredType, unqualifyPredType
  , PredTypes (..), qualifyPredTypes, unqualifyPredTypes
    -- * Representation of data constructors
  , DataConstr (..), constrIdent, constrTypes, recLabels, recLabelTypes
  , tupleData
    -- * Representation of class methods
  , ClassMethod (..), methodName, methodArity, methodType
    -- * Representation of quantification
  , TypeScheme (..), monoType, polyType, typeScheme
  , rawType
    -- * Predefined types
  , arrowType, unitType, predUnitType, boolType, predBoolType, charType
  , intType, predIntType, floatType, predFloatType, stringType, predStringType
  , listType, consType, ioType, tupleType
  , numTypes, fractionalTypes
  , predefTypes
  ) where

import           Data.Function (on)
import           Data.List (nub, partition, (\\))
import qualified Data.Set.Extra as Set

import Control.Monad ( liftM )

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Base.SpanInfo

import Base.Messages (internalError)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- A type is either a type constructor, a type variable, an application
-- of a type to another type, or an arrow type. Although the latter could
-- be expressed by using 'TypeApply' with the function type constructor,
-- we currently use 'TypeArrow' because arrow types are used so frequently.

-- The 'TypeConstrained' case is used for representing type variables that
-- are restricted to a particular set of types. At present, this is used
-- for typing integer literals, which are restricted to types 'Int' and
-- 'Float'. If the type is not restricted, it defaults to the first type
-- from the constraint list.

-- Type variables are represented with deBruijn style indices. Universally
-- quantified type variables are assigned indices in the order of their
-- occurrence in the type from left to right. This leads to a canonical
-- representation of types where alpha-equivalence of two types
-- coincides with equality of the representation.

-- Note that even though 'TypeConstrained' variables use indices
-- as well, these variables must never be quantified.

-- Note further that the order of constructors is important for the derived
-- 'Ord' instance. In particular, it is essential that the type variable
-- is considered less than the type application (see predicates and predicate
-- sets below for more information).

data Type
  = TypeConstructor QualIdent
  | TypeVariable Int
  | TypeConstrained [Type] Int
  | TypeApply Type Type
  | TypeArrow Type Type
  | TypeForall [Int] Type
  deriving (Eq, Ord, Show)

-- The function 'applyType' applies a type to a list of argument types,
-- whereas applications of the function type constructor to two arguments
-- are converted into an arrow type. The function 'unapplyType' decomposes
-- a type into a root type and a list of argument types.

applyType :: Type -> [Type] -> Type
applyType (TypeConstructor tc) tys
  | tc == qArrowId && length tys == 2 = TypeArrow (tys !! 0) (tys !! 1)
applyType (TypeApply (TypeConstructor tc) ty) tys
  | tc == qArrowId && length tys == 1 = TypeArrow ty (head tys)
applyType ty tys = foldl TypeApply ty tys

unapplyType :: Bool -> Type -> (Type, [Type])
unapplyType dflt ty = unapply ty []
  where
    unapply (TypeConstructor     tc) tys  = (TypeConstructor tc, tys)
    unapply (TypeApply      ty1 ty2) tys  = unapply ty1 (ty2 : tys)
    unapply (TypeVariable        tv) tys  = (TypeVariable tv, tys)
    unapply (TypeArrow      ty1 ty2) tys  =
      (TypeConstructor qArrowId, ty1 : ty2 : tys)
    unapply (TypeConstrained tys tv) tys'
      | dflt      = unapply (head tys) tys'
      | otherwise = (TypeConstrained tys tv, tys')
    unapply (TypeForall     tvs ty') tys  = (TypeForall tvs ty', tys)

-- Checks if a type is a simple type variable.
-- taken from Leif-Erik Krueger
isTypeVariable :: Type -> Bool
isTypeVariable (TypeVariable _) = True
isTypeVariable _                = False

-- Checks if a type is a type variable or a type variable applied to types.
-- Taken from Leif-Erik Krueger
isAppliedTypeVariable :: Type -> Bool
isAppliedTypeVariable = isTypeVariable . fst . unapplyType False



-- The function 'rootOfType' returns the name of the type constructor at the
-- root of a type. This function must not be applied to a type whose root is
-- a type variable or a skolem type.

rootOfType :: Type -> QualIdent
rootOfType ty = case fst (unapplyType True ty) of
  TypeConstructor tc -> tc
  _ -> internalError $ "Base.Types.rootOfType: " ++ show ty

-- The function 'isArrowType' checks whether a type is a function
-- type t_1 -> t_2 -> ... -> t_n. The function 'arrowArity' computes
-- the arity n of a function type, 'arrowArgs' computes the types
-- t_1 ... t_n-1 and 'arrowBase' returns the type t_n. 'arrowUnapply'
-- combines 'arrowArgs' and 'arrowBase' in one call.

isArrowType :: Type -> Bool
isArrowType (TypeArrow _ _) = True
isArrowType _               = False

arrowArity :: Type -> Int
arrowArity = length. arrowArgs

arrowArgs :: Type -> [Type]
arrowArgs = fst . arrowUnapply

arrowBase :: Type -> Type
arrowBase = snd. arrowUnapply

arrowUnapply :: Type -> ([Type], Type)
arrowUnapply (TypeArrow ty1 ty2) = (ty1 : tys, ty)
  where (tys, ty) = arrowUnapply ty2
arrowUnapply ty                  = ([], ty)

-- The function 'typeConstrs' returns a list of all type constructors
-- occurring in a type t.

typeConstrs :: Type -> [QualIdent]
typeConstrs ty = constrs ty [] where
  constrs (TypeConstructor  tc) tcs = tc : tcs
  constrs (TypeApply   ty1 ty2) tcs = constrs ty1 (constrs ty2 tcs)
  constrs (TypeVariable      _) tcs = tcs
  constrs (TypeConstrained _ _) tcs = tcs
  constrs (TypeArrow   ty1 ty2) tcs = constrs ty1 (constrs ty2 tcs)
  constrs (TypeForall    _ ty') tcs = constrs ty' tcs

-- taken from Leif-Erik Krueger
removeTypeConstrained :: Type -> Type
removeTypeConstrained t@(TypeConstructor  _) = t
removeTypeConstrained t@(TypeVariable     _) = t
removeTypeConstrained (TypeConstrained _ tv) = TypeVariable tv
removeTypeConstrained (TypeApply      t1 t2) =
  TypeApply (removeTypeConstrained t1) (removeTypeConstrained t2)
removeTypeConstrained (TypeArrow      t1 t2) =
  TypeArrow (removeTypeConstrained t1) (removeTypeConstrained t2)
removeTypeConstrained (TypeForall     tvs t) =
  TypeForall tvs (removeTypeConstrained t)


-- The method 'typeVars' returns a list of all type variables occurring in a
-- type t. Note that 'TypeConstrained' variables are not included in the set of
-- type variables because they cannot be generalized.

class IsType t where
  typeVars :: t -> [Int]

instance IsType Type where
  typeVars = typeVars'

typeVars' :: Type -> [Int]
typeVars' ty = vars ty [] where
  vars (TypeConstructor   _) tvs = tvs
  vars (TypeApply   ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
  vars (TypeVariable     tv) tvs = tv : tvs
  vars (TypeConstrained _ _) tvs = tvs
  vars (TypeArrow   ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
  vars (TypeForall tvs' ty') tvs = filter (`notElem` tvs') (typeVars' ty') ++ tvs

-- The functions 'qualifyType' and 'unqualifyType' add/remove the
-- qualification with a module identifier for type constructors.

qualifyType :: ModuleIdent -> Type -> Type
qualifyType m (TypeConstructor     tc) = TypeConstructor (qualifyTC m tc)
qualifyType m (TypeApply      ty1 ty2) =
  TypeApply (qualifyType m ty1) (qualifyType m ty2)
qualifyType _ tv@(TypeVariable      _) = tv
qualifyType m (TypeConstrained tys tv) =
  TypeConstrained (map (qualifyType m) tys) tv
qualifyType m (TypeArrow      ty1 ty2) =
  TypeArrow (qualifyType m ty1) (qualifyType m ty2)
qualifyType m (TypeForall      tvs ty) = TypeForall tvs (qualifyType m ty)

unqualifyType :: ModuleIdent -> Type -> Type
unqualifyType m (TypeConstructor     tc) = TypeConstructor (qualUnqualify m tc)
unqualifyType m (TypeApply      ty1 ty2) =
  TypeApply (unqualifyType m ty1) (unqualifyType m ty2)
unqualifyType _ tv@(TypeVariable      _) = tv
unqualifyType m (TypeConstrained tys tv) =
  TypeConstrained (map (unqualifyType m) tys) tv
unqualifyType m (TypeArrow      ty1 ty2) =
  TypeArrow (unqualifyType m ty1) (unqualifyType m ty2)
unqualifyType m (TypeForall      tvs ty) = TypeForall tvs (unqualifyType m ty)

qualifyTC :: ModuleIdent -> QualIdent -> QualIdent
qualifyTC m tc | isPrimTypeId tc = tc
               | otherwise       = qualQualify m tc

-- ---------------------------------------------------------------------------
-- Predicates
-- ---------------------------------------------------------------------------

-- Predicates use a flag which marks whether the predicate is the implicit class
-- constraint of a class method. This flag is positioned as the first field of
-- the predicate data constructor, which ensures such an implicit class
-- constraint is always the minimum w.r.t. the order of the derived 'Ord'
-- instance (see predicate sets below for more information why this order is
-- relevant).

data Pred = Pred PredIsICC QualIdent [Type]
  deriving (Eq, Ord, Show)

-- Short for: data PredicateIsImplicitClassConstraint = ImplicitClassConstraint
--                                                    | OtherPredicate
data PredIsICC = ICC | OPred
  deriving (Eq, Ord, Show)

instance IsType Pred where
  typeVars (Pred _ _ tys) = typeVars tys

instance IsType a => IsType [a] where
  typeVars = concatMap typeVars

-- In addition to a predicate, located predicates contain information about the
-- source code location where the predicate came from, which can be used in
-- error messages. For the 'Eq' and 'Ord' instances of located predicates, only
-- the predicate part is compared, so that the same predicate coming from
-- multiple different source code locations does only occur once in predicate
-- sets.

data LPred = LPred Pred SpanInfo String Doc
  deriving Show

instance Eq LPred where
  (==) = (==) `on` getPred

instance Ord LPred where
  compare = compare `on` getPred

-- The 'IsPred' class provides a common interface for 'Pred's and 'LPred's,
-- so that many functions can be applied to both kinds of predicates and
-- predicate sets.
class (Ord a, IsType a) => IsPred a where
  getPred :: a -> Pred
  -- TODO: Is there a better name? (Should have been 'fromPred', which is taken)
  getFromPred :: Pred -> a
  modifyPred :: (Pred -> Pred) -> a -> a

instance IsPred Pred where
  getPred = id
  getFromPred = id
  modifyPred = id

instance IsPred LPred where
  getPred (LPred pr _ _ _) = pr
  getFromPred pr = LPred pr NoSpanInfo "" empty
  modifyPred f (LPred pr spi what doc) = LPred (f pr) spi what doc

instance IsType LPred where
  typeVars = typeVars . getPred

qualifyPred :: IsPred a => ModuleIdent -> a -> a
qualifyPred m = modifyPred $
  \(Pred isIcc qcls tys) ->
    Pred isIcc (qualQualify m qcls) (map (qualifyType m) tys)

unqualifyPred :: IsPred a => ModuleIdent -> a -> a
unqualifyPred m = modifyPred $
  \(Pred isIcc qcls tys) ->
    Pred isIcc (qualUnqualify m qcls) (map (unqualifyType m) tys)

-- ---------------------------------------------------------------------------
-- Predicate sets
-- ---------------------------------------------------------------------------

-- A predicate set is an ordered set of predicates. This way, we do not
-- have to manually take care of duplicate predicates and have automatically
-- achieved a canonical representation (as only original names for type classes
-- are used). Having the order on types and predicates in mind, we have also
-- ensured that a class method's implicit class constraint is always the minimum
-- element of a method's predicate set, thus making it very easy to remove it.

type PredSet = Set.Set Pred

type LPredSet = Set.Set LPred

type PredList = [Pred]

type LPredList = [LPred]

instance (IsType a, Ord a) => IsType (Set.Set a) where
  typeVars = concat . Set.toList . Set.map typeVars

emptyPredSet :: PredSet
emptyPredSet = Set.empty

emptyLPredSet :: LPredSet
emptyLPredSet = Set.empty

-- Checks if a predicate is a member of a predicate set ignoring the 'PredIsICC'
-- flag.
psMember :: (IsPred a, IsPred b) => a -> Set.Set b -> Bool
psMember pr ps = let Pred _ qcls tys = getPred pr
                     psMember' :: Pred -> Pred -> Bool
                     psMember' = (||) `on` ((`Set.member` ps) . getFromPred)
                 in psMember' (Pred OPred qcls tys) (Pred ICC qcls tys)

-- Same as above for lists
plElem :: (IsPred a, IsPred b) => a -> [b] -> Bool
plElem pr pl = let Pred _ qcls tys = getPred pr
                   plElem' :: Pred -> Pred -> Bool
                   plElem' = (||) `on` ((`elem` pl) . getFromPred)
               in plElem' (Pred OPred qcls tys) (Pred ICC qcls tys)

-- Returns the given predicate set with its implicit class constraint, if it has
-- any, transformed into a regular predicate.
removeICCFlag :: IsPred a => Set.Set a -> Set.Set a
removeICCFlag ps = case Set.lookupMin ps of
  Just pr | (\(Pred isIcc _ _) -> isIcc == ICC) (getPred pr) ->
    Set.insert (modifyPred (\(Pred _ qcls tys) -> Pred OPred qcls tys) pr)
               (Set.deleteMin ps)
  _ -> ps

-- the same as above, but for lists
removeICCFlagList :: IsPred a => [a] -> [a]
removeICCFlagList []                            = []
removeICCFlagList (p : ps)
  | iccFlag == ICC = (modifyPred (\(Pred _ qcls tys) -> Pred OPred qcls tys) p) : ps
  | otherwise      = p : removeICCFlagList ps
 where
  iccFlag = let Pred icc _ _ = getPred p in icc

-- Partitions the predicate set given as the second argument such that all
-- predicates in the first element of the returned tuple are elements of the
-- predicate set given as the first argument or have at least one predicate type
-- that is a type variable (or a type variable applied to types).
--
-- This function is used during the type check to report missing instances when
-- it is possible that only some of the predicate types have been inferred. The
-- first predicate set given is used to not report predicates without fitting
-- instances, if they are mentioned as constraints of an explicit type
-- signature.

-- Partitions the given predicate set such that all predicates in the first
-- element of the returned tuple have only type variables (or type variables
-- applied to types) as predicate types.
--
-- This function is used to report constraints that would only be allowed with
-- a FlexibleContexts language extension when all predicate types are known.

-- taken from Leif-Erik Krueger
partitionPredList :: IsPred a => [a] -> ([a],[a])
partitionPredList = partition $ 
  (\(Pred _ _ tys) -> all isAppliedTypeVariable tys) . getPred

-------------------------------------------------------------------------------
-- Operations on predicate lists
-------------------------------------------------------------------------------

-- The set theoretical union of two predicateList
-- TODO : check if this can be changed so that predicates are ordered by
-- the order in a given type scheme.
plUnion :: Eq a => [a] -> [a] -> [a]
plUnion pl1 pl2 = nub (pl1 ++ pl2)

-- Set-theoretical difference of two predicate lists
plDifference :: Eq a => [a] -> [a] -> [a]
plDifference = (\\)

-- Insert an element into a predicate list and remove all duplicates afterwards
plInsert :: Eq a => a -> [a] -> [a]
plInsert pl pls = nub (pl:pls)

-- The list version of plUnion
plUnions :: Eq a => [[a]] -> [a]
plUnions = foldr plUnion []

-- concatMap for predicate lists
plConcatMap :: Eq b => (a -> [b]) -> [a] -> [b]
plConcatMap f = plUnions . map f 

-- concatMapM for predicate lists
plConcatMapM :: (Eq b, Monad m) => (a -> m [b]) -> [a] -> m [b]
plConcatMapM f = liftM plUnions . mapM f

-- lookup the minimum element of a predicate list. If the list contains a
-- predicate that can be ordered
plLookupMin :: Ord a => [a] -> Maybe a
plLookupMin []       = Nothing
plLookupMin xs@(_:_) = Just $ minimum xs

-- delete the minimal element of a predicate list
plDeleteMin :: Ord a => [a] -> [a]
plDeleteMin pls = case minIndex pls of
    Nothing -> pls
    Just i  -> deleteIndex i pls
  where
    minIndex :: Ord b => [b] -> Maybe Int
    minIndex [] = Nothing
    minIndex (p : pl) = Just $ minIndex' pl p 0 1

    minIndex' :: Ord b => [b] -> b -> Int -> Int -> Int
    minIndex' []     _  i _ = i
    minIndex' (p:ps) p' i j | p < p'    = minIndex' ps p j (j+1)
                            | otherwise = minIndex' ps p' i (j+1)
    
    deleteIndex _ []     = []
    deleteIndex 0 (_:xs) = xs
    deleteIndex n (x:xs) = x : deleteIndex (n-1) xs

plDelete :: Eq a => a -> [a] -> [a]
plDelete _ []     = []
plDelete x (y:ys) | x == y    = plDelete x ys
                  | otherwise = y : plDelete x ys

qualifyPredSet :: IsPred a => ModuleIdent -> Set.Set a -> Set.Set a
qualifyPredSet m = Set.map (qualifyPred m)

unqualifyPredSet :: IsPred a => ModuleIdent -> Set.Set a -> Set.Set a
unqualifyPredSet m = Set.map (unqualifyPred m)

qualifyPredList :: IsPred a => ModuleIdent -> [a] -> [a]
qualifyPredList m = map (qualifyPred m)

unqualifyPredList :: IsPred a => ModuleIdent -> [a] -> [a]
unqualifyPredList m = map (unqualifyPred m)

-- ---------------------------------------------------------------------------
-- Predicated types
-- ---------------------------------------------------------------------------

data PredType = PredType [Pred] Type
  deriving (Eq, Show)

-- When enumarating the type variables and skolems of a predicated type, we
-- consider the type variables occurring in the predicate set after the ones
-- occurring in the type itself.

instance IsType PredType where
  typeVars (PredType pls ty) = typeVars ty ++ typeVars pls

predType :: Type -> PredType
predType = PredType []

unpredType :: PredType -> Type
unpredType (PredType _ ty) = ty

qualifyPredType :: ModuleIdent -> PredType -> PredType
qualifyPredType m (PredType pls ty) =
  PredType (qualifyPredList m pls) (qualifyType m ty)

unqualifyPredType :: ModuleIdent -> PredType -> PredType
unqualifyPredType m (PredType pls ty) =
  PredType (unqualifyPredList m pls) (unqualifyType m ty)

-- The 'PredTypes' data type stores a predicate list and a list of types all
-- constrained by this predicate set. It can be used to represent the context
-- and the instance types of an instance declaration.
data PredTypes = PredTypes PredList [Type]

instance IsType PredTypes where
  typeVars (PredTypes pls tys) = typeVars tys ++ typeVars pls

qualifyPredTypes :: ModuleIdent -> PredTypes -> PredTypes
qualifyPredTypes m (PredTypes pls tys) =
  PredTypes (qualifyPredList m pls) (map (qualifyType m) tys)

unqualifyPredTypes :: ModuleIdent -> PredTypes -> PredTypes
unqualifyPredTypes m (PredTypes pls tys) =
  PredTypes (unqualifyPredList m pls) (map (unqualifyType m) tys)

-- ---------------------------------------------------------------------------
-- Data constructors
-- ---------------------------------------------------------------------------

-- The type 'DataConstr' is used to represent value or record constructors
-- introduced by data or newtype declarations.

data DataConstr = DataConstr   Ident [Type]
                | RecordConstr Ident [Ident] [Type]
  deriving (Eq, Show)

constrIdent :: DataConstr -> Ident
constrIdent (DataConstr     c _) = c
constrIdent (RecordConstr c _ _) = c

constrTypes :: DataConstr -> [Type]
constrTypes (DataConstr     _ tys) = tys
constrTypes (RecordConstr _ _ tys) = tys

recLabels :: DataConstr -> [Ident]
recLabels (DataConstr      _ _) = []
recLabels (RecordConstr _ ls _) = ls

recLabelTypes :: DataConstr -> [Type]
recLabelTypes (DataConstr       _ _) = []
recLabelTypes (RecordConstr _ _ tys) = tys

tupleData :: [DataConstr]
tupleData = [DataConstr (tupleId n) (take n tvs) | n <- [2 ..]]
  where tvs = map TypeVariable [0 ..]

-- ---------------------------------------------------------------------------
-- Class methods
-- ---------------------------------------------------------------------------

-- The type 'ClassMethod' is used to represent class methods introduced
-- by class declarations. The 'Maybe Int' denotes the arity of the provided
-- default implementation.

data ClassMethod = ClassMethod Ident (Maybe Int) PredType
  deriving (Eq, Show)

methodName :: ClassMethod -> Ident
methodName (ClassMethod f _ _) = f

methodArity :: ClassMethod -> Maybe Int
methodArity (ClassMethod _ a _) = a

methodType :: ClassMethod -> PredType
methodType (ClassMethod _ _ pty) = pty

-- ---------------------------------------------------------------------------
-- Quantification
-- ---------------------------------------------------------------------------

-- We support only universally quantified type schemes
-- (forall alpha . tau(alpha)). Quantified type variables are assigned
-- ascending indices starting from 0. Therefore it is sufficient to record the
-- numbers of quantified type variables in the 'ForAll' constructor.

data TypeScheme = ForAll Int PredType deriving (Eq, Show)

instance IsType TypeScheme where
  typeVars (ForAll _ pty) = [tv | tv <- typeVars pty, tv < 0]

-- The functions 'monoType' and 'polyType' translate a type tau into a
-- monomorphic type scheme and a polymorphic type scheme, respectively.
-- 'polyType' assumes that all universally quantified variables in the type are
-- assigned indices starting with 0 and does not renumber the variables.

monoType :: Type -> TypeScheme
monoType = ForAll 0 . predType

polyType :: Type -> TypeScheme
polyType = typeScheme . predType

typeScheme :: PredType -> TypeScheme
typeScheme pty = ForAll (maximum (-1 : typeVars pty) + 1) pty

-- The function 'rawType' strips the quantifier and predicate set from a
-- type scheme.

rawType :: TypeScheme -> Type
rawType (ForAll _ (PredType _ ty)) = ty

-- ---------------------------------------------------------------------------
-- Predefined types
-- ---------------------------------------------------------------------------

primType :: QualIdent -> [Type] -> Type
primType = applyType . TypeConstructor

arrowType :: Type -> Type -> Type
arrowType ty1 ty2 = primType qArrowId [ty1, ty2]

unitType :: Type
unitType = primType qUnitId []

predUnitType :: PredType
predUnitType = predType unitType

boolType :: Type
boolType = primType qBoolId []

predBoolType :: PredType
predBoolType = predType boolType

charType :: Type
charType = primType qCharId []

intType :: Type
intType = primType qIntId []

predIntType :: PredType
predIntType = predType intType

floatType :: Type
floatType = primType qFloatId []

predFloatType :: PredType
predFloatType = predType floatType

stringType :: Type
stringType = listType charType

predStringType :: PredType
predStringType = predType stringType

listType :: Type -> Type
listType ty = primType qListId [ty]

consType :: Type -> Type
consType ty = TypeArrow ty (TypeArrow (listType ty) (listType ty))

ioType :: Type -> Type
ioType ty = primType qIOId [ty]

tupleType :: [Type] -> Type
tupleType tys = primType (qTupleId (length tys)) tys

-- 'numTypes' and 'fractionalTypes' define the eligible types for
-- numeric literals in patterns.

numTypes :: [Type]
numTypes = [intType, floatType]

fractionalTypes :: [Type]
fractionalTypes = drop 1 numTypes

predefTypes :: [(Type, [DataConstr])]
predefTypes =
  [ (arrowType a b, [])
  , (unitType     , [ DataConstr unitId [] ])
  , (listType a   , [ DataConstr nilId  []
                    , DataConstr consId [a, listType a]
                    ])
  ]
  where a = TypeVariable 0
        b = TypeVariable 1
