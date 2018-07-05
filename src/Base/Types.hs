{- |
    Module      :  $Header$
    Description :  Internal representation of types
    Copyright   :  (c) 2002 - 2004 Wolfgang Lux
                                   Martin Engelke
                       2015        Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module modules provides the definitions for the internal
   representation of types in the compiler.
-}

-- TODO: Use MultiParamTypeClasses ?

{-# LANGUAGE CPP #-}
module Base.Types
  ( -- * Representation of Types
    Type (..), isArrowType, arrowArity, arrowArgs, arrowBase, arrowUnapply
  , fromType, typeVars, typeConstrs, typeSkolems, equTypes, qualifyType
  , unqualifyType
    -- * Representation of Data Constructors
  , DataConstr (..), constrIdent, constrTypes, recLabels, recLabelTypes
  , tupleData
    -- * Representation of Quantification
  , TypeScheme (..), ExistTypeScheme (..), monoType, polyType
    -- * Predefined types
  , unitType, boolType, charType, intType, floatType, stringType
  , listType, ioType, tupleType, typeVar, predefTypes
  ) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import Curry.Base.Ident
import Curry.Base.Pretty   (Pretty(..))
import qualified Curry.Syntax as CS
import Curry.Syntax.Pretty (ppTypeExpr)

import Text.PrettyPrint

-- A type is either a type variable, an application of a type constructor
-- to a list of arguments, or an arrow type. The 'TypeConstrained'
-- case is used for representing type variables that are restricted to a
-- particular set of types. At present, this is used for typing
-- integer literals, which are restricted to types 'Int' and
-- 'Float'. If the type is not restricted, it defaults to the first type
-- from the constraint list.
-- The case 'TypeSkolem' is used for handling skolem types, which
-- result from the use of existentially quantified data constructors.

-- Type variables are represented with deBruijn style indices. Universally
-- quantified type variables are assigned indices in the order of their
-- occurrence in the type from left to right. This leads to a canonical
-- representation of types where alpha-equivalence of two types
-- coincides with equality of the representation.

-- Note that even though 'TypeConstrained' variables use indices
-- as well, these variables must never be quantified.

data Type
  = TypeVariable Int
  | TypeConstructor QualIdent [Type]
  | TypeArrow Type Type
  | TypeConstrained [Type] Int
  | TypeSkolem Int
  deriving (Eq, Show)

instance Pretty Type where
  pPrint = ppTypeExpr 0 . fromType

fromType :: Type -> CS.TypeExpr
fromType (TypeConstructor tc tys)
  | isTupleId c                    = CS.TupleType tys'
  | c == unitId && null tys        = CS.TupleType []
  | c == listId && length tys == 1 = CS.ListType (head tys')
  | otherwise                      = CS.ConstructorType tc tys'
  where c    = unqualify tc
        tys' = map fromType tys
fromType (TypeVariable tv)         = CS.VariableType
   (if tv >= 0 then identSupply !! tv else mkIdent ('_' : show (-tv)))
fromType (TypeConstrained tys _)   = fromType (head tys)
fromType (TypeArrow     ty1 ty2)   =
  CS.ArrowType (fromType ty1) (fromType ty2)
fromType (TypeSkolem          k)   =
  CS.VariableType $ mkIdent $ "_?" ++ show k

-- The function 'isArrowType' checks whether a type is a function
-- type t_1 -> t_2 -> ... -> t_n . The function 'arrowArity' computes the arity
-- n of a function type, 'arrowArgs' computes the types t_1 ... t_n-1
-- and 'arrowBase' returns the type t_n.

isArrowType :: Type -> Bool
isArrowType (TypeArrow _ _) = True
isArrowType _               = False

arrowArity :: Type -> Int
arrowArity (TypeArrow _ ty) = 1 + arrowArity ty
arrowArity _                = 0

arrowArgs :: Type -> [Type]
arrowArgs (TypeArrow ty1 ty2) = ty1 : arrowArgs ty2
arrowArgs _                   = []

arrowBase :: Type -> Type
arrowBase (TypeArrow _ ty) = arrowBase ty
arrowBase ty               = ty

arrowUnapply :: Type -> ([Type], Type)
arrowUnapply (TypeArrow ty1 ty2) = (ty1 : tys, ty)
  where (tys, ty) = arrowUnapply ty2
arrowUnapply ty                  = ([], ty)

-- The functions 'typeVars', 'typeConstrs', 'typeSkolems' return a list of all
-- type variables, type constructors, or skolems occurring in a type t,
-- respectively. Note that 'TypeConstrained' variables are not included in the
-- set of type variables because they cannot be generalized.

typeVars :: Type -> [Int]
typeVars ty = vars ty [] where
  vars (TypeConstructor _ tys) tvs = foldr vars tvs tys
  vars (TypeVariable       tv) tvs = tv : tvs
  vars (TypeConstrained   _ _) tvs = tvs
  vars (TypeArrow     ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
  vars (TypeSkolem          _) tvs = tvs

typeConstrs :: Type -> [QualIdent]
typeConstrs ty = constrs ty [] where
  constrs (TypeConstructor tc tys) tcs = tc : foldr constrs tcs tys
  constrs (TypeVariable         _) tcs = tcs
  constrs (TypeConstrained    _ _) tcs = tcs
  constrs (TypeArrow      ty1 ty2) tcs = constrs ty1 (constrs ty2 tcs)
  constrs (TypeSkolem           _) tcs = tcs

typeSkolems :: Type -> [Int]
typeSkolems ty = skolems ty [] where
  skolems (TypeConstructor _ tys) sks = foldr skolems sks tys
  skolems (TypeVariable        _) sks = sks
  skolems (TypeConstrained   _ _) sks = sks
  skolems (TypeArrow     ty1 ty2) sks = skolems ty1 (skolems ty2 sks)
  skolems (TypeSkolem          k) sks = k : sks

-- The function 'equTypes' computes whether two types are equal modulo
-- renaming of type variables.
equTypes :: Type -> Type -> Bool
equTypes t1 t2 = fst (equ [] t1 t2)
 where
 -- @is@ is an AssocList of type variable indices
 equ is (TypeConstructor qid1 ts1) (TypeConstructor qid2 ts2)
   | qid1 == qid2 = equs is ts1 ts2
   | otherwise    = (False, is)
 equ is (TypeVariable          i1) (TypeVariable          i2)
   = equVar is i1 i2
 equ is (TypeConstrained   ts1 i1) (TypeConstrained   ts2 i2)
   = let (res , is1) = equs   is  ts1 ts2
         (res2, is2) = equVar is1 i1  i2
     in  (res && res2, is2)
 equ is (TypeArrow        tf1 tt1) (TypeArrow        tf2 tt2)
   = let (res1, is1) = equ is  tf1 tf2
         (res2, is2) = equ is1 tt1 tt2
     in  (res1 && res2, is2)
 equ is (TypeSkolem            i1) (TypeSkolem            i2)
  = equVar is i1 i2
 equ is _                          _
  = (False, is)

 equVar is i1 i2 = case lookup i1 is of
   Nothing  -> (True, (i1, i2) : is)
   Just i2' -> (i2 == i2', is)

 equs is []        []        = (True , is)
 equs is (t1':ts1) (t2':ts2)
    = let (res1, is1) = equ  is t1'  t2'
          (res2, is2) = equs is1 ts1 ts2
      in  (res1 && res2, is2)
 equs is _         _         = (False, is)

-- The functions 'qualifyType' and 'unqualifyType' add/remove the
-- qualification with a module identifier for type constructors.

qualifyType :: ModuleIdent -> Type -> Type
qualifyType m (TypeConstructor tc tys)
  | isTupleId tc'           = tupleType tys'
  | tc' == unitId && n == 0 = unitType
  | tc' == listId && n == 1 = listType (head tys')
  | otherwise = TypeConstructor (qualQualify m tc) tys'
  where n    = length tys'
        tc'  = unqualify tc
        tys' = map (qualifyType m) tys
qualifyType _ var@(TypeVariable     _) = var
qualifyType m (TypeConstrained tys tv) =
  TypeConstrained (map (qualifyType m) tys) tv
qualifyType m (TypeArrow      ty1 ty2) =
  TypeArrow (qualifyType m ty1) (qualifyType m ty2)
qualifyType _ skol@(TypeSkolem      _) = skol

unqualifyType :: ModuleIdent -> Type -> Type
unqualifyType m (TypeConstructor tc tys) =
  TypeConstructor (qualUnqualify m tc) (map (unqualifyType m) tys)
unqualifyType _ var@(TypeVariable     _) = var
unqualifyType m (TypeConstrained tys tv) =
  TypeConstrained (map (unqualifyType m) tys) tv
unqualifyType m (TypeArrow      ty1 ty2) =
  TypeArrow (unqualifyType m ty1) (unqualifyType m ty2)
unqualifyType _ skol@(TypeSkolem      _) = skol

-- The type 'DataConstr' is used to represent value or record constructors
-- introduced by data or newtype declarations.
data DataConstr = DataConstr   Ident Int [Type]
                | RecordConstr Ident Int [Ident] [Type]
    deriving (Eq, Show)

instance Pretty DataConstr where
  pPrint (DataConstr i _ tys)      = pPrint i <+> hsep (map pPrint tys)
  pPrint (RecordConstr i _ ls tys) =     pPrint i
                                     <+> braces (hsep (punctuate comma pLs))
    where
      pLs = zipWith (\l ty -> pPrint l <+> colon <> colon <+> pPrint ty) ls tys

constrIdent :: DataConstr -> Ident
constrIdent (DataConstr     c _ _) = c
constrIdent (RecordConstr c _ _ _) = c

constrTypes :: DataConstr -> [Type]
constrTypes (DataConstr     _ _ ty) = ty
constrTypes (RecordConstr _ _ _ ty) = ty

recLabels :: DataConstr -> [Ident]
recLabels (DataConstr      _ _ _) = []
recLabels (RecordConstr _ _ ls _) = ls

recLabelTypes :: DataConstr -> [Type]
recLabelTypes (DataConstr       _ _ _) = []
recLabelTypes (RecordConstr _ _ _ tys) = tys

-- We support two kinds of quantifications of types here, universally
-- quantified type schemes (forall alpha . tau(alpha)) and universally
-- and existentially quantified type schemes
-- (forall alpha exists eta . tau(alpha,eta)). In both, quantified type
-- variables are assigned ascending indices starting from 0. Therefore it
-- is sufficient to record the numbers of quantified type variables in
-- the 'ForAll' and 'ForAllExist' constructors. In case of
-- the latter, the first of the two numbers is the number of universally
-- quantified variables and the second the number of existentially
-- quantified variables.

data TypeScheme = ForAll Int Type deriving (Eq, Show)
data ExistTypeScheme = ForAllExist Int Int Type deriving (Eq, Show)

instance Pretty TypeScheme where
  pPrint (ForAll _ ty) = pPrint ty

instance Pretty ExistTypeScheme where
  pPrint (ForAllExist _ _ ty) = pPrint ty

-- The functions 'monoType' and 'polyType' translate a type tau into a
-- monomorphic type scheme and a polymorphic type scheme, respectively.
-- 'polyType' assumes that all universally quantified variables in the type are
-- assigned indices starting with 0 and does not renumber the variables.

monoType :: Type -> TypeScheme
monoType ty = ForAll 0 ty

polyType :: Type -> TypeScheme
polyType ty = ForAll (maximum (-1 : typeVars ty) + 1) ty

-- There are a few predefined types:

unitType :: Type
unitType = primType qUnitId []

boolType :: Type
boolType = primType qBoolId []

charType :: Type
charType = primType qCharId []

intType :: Type
intType = primType qIntId []

floatType :: Type
floatType = primType qFloatId []

stringType :: Type
stringType = listType charType

listType :: Type -> Type
listType ty = primType qListId [ty]

ioType :: Type -> Type
ioType ty = primType qIOId [ty]

tupleType :: [Type] -> Type
tupleType tys = primType (qTupleId (length tys)) tys

typeVar :: Int -> Type
typeVar = TypeVariable

primType :: QualIdent -> [Type] -> Type
primType = TypeConstructor --  . qualifyWith preludeMIdent

predefTypes :: [(Type, [DataConstr])]
predefTypes = let a = typeVar 0 in
  [ (unitType  , [ DataConstr unitId 0 [] ])
  , (listType a, [ DataConstr nilId  0 []
                 , DataConstr consId 0 [a, listType a]
                 ])
  ]

tupleData :: [DataConstr]
tupleData = [DataConstr (tupleId n) n (take n tvs) | n <- [2 ..]]
  where tvs = map typeVar [0 ..]
