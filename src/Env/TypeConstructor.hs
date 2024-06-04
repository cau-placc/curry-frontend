{- |
    Module      :  $Header$
    Description :  Environment of type constructors
    Copyright   :  (c) 2002 - 2004 Wolfgang Lux
                       2011        Björn Peemöller
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    For all defined types the compiler must maintain kind information.
    For algebraic data types and renaming types the compiler also records
    all data constructors belonging to that type, for alias types the
    type expression to be expanded is saved. Futhermore, recording the
    arity is necessary for alias types because the right hand side, i.e.,
    the type expression, can have arbitrary kind and therefore the type
    alias' arity cannot be determined from its own kind. For instance,
    the type alias type List = [] has the kind * -> *, but its arity is 0.
    In order to manage the import and export of types, the names of the
    original definitions are also recorded. On import two types are
    considered equal if their original names match.

    The information for a data constructor comprises the number of
    existentially quantified type variables, the context and the list
    of the argument types. Note that renaming type constructors have only
    one type argument.

    For type classes the all their methods are saved. Type classes are
    recorded in the type constructor environment because type constructors
    and type classes share a common name space.

    For type variables only their kind is recorded in the environment.

    Importing and exporting algebraic data types and renaming types is
    complicated by the fact that the constructors of the type may be
    (partially) hidden in the interface. This facilitates the definition
    of abstract data types. An abstract type is always represented as a
    data type without constructors in the interface regardless of whether
    it is defined as a data type or as a renaming type. When only some
    constructors of a data type are hidden, those constructors are
    replaced by underscores in the interface. Furthermore, if the
    right-most constructors of a data type are hidden, they are not
    exported at all in order to make the interface more stable against
    changes which are private to the module.
-}
{-# LANGUAGE CPP #-}
module Env.TypeConstructor
  ( TypeInfo (..), tcKind, clsKind, varKind, clsMethods
  , TCEnv, initTCEnv, bindTypeInfo, rebindTypeInfo
  , lookupTypeInfo, qualLookupTypeInfo, qualLookupTypeInfoUnique
  , getOrigName, reverseLookupByOrigName
  ) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import Curry.Base.Ident
import Curry.Base.Pretty (Pretty(..), blankLine)

import Base.Kinds
import Base.Messages (internalError)
import Base.PrettyKinds ()
import Base.PrettyTypes ()
import Base.TopEnv
import Base.Types
import Base.Utils         ((++!))

import Text.PrettyPrint

data TypeInfo
  = DataType     QualIdent Kind [DataConstr]
  | RenamingType QualIdent Kind DataConstr
  | AliasType    QualIdent Kind Int Type
  | TypeClass    QualIdent Kind [ClassMethod]
  | TypeVar      Kind
    deriving Show

instance Entity TypeInfo where
  origName (DataType     tc    _ _) = tc
  origName (RenamingType tc    _ _) = tc
  origName (AliasType    tc  _ _ _) = tc
  origName (TypeClass    cls   _ _) = cls
  origName (TypeVar              _) =
    internalError "Env.TypeConstructor.origName: type variable"

  merge (DataType tc k cs) (DataType tc' k' cs')
    | tc == tc' && k == k' && (null cs || null cs' || cs == cs') =
    Just $ DataType tc k $ if null cs then cs' else cs
  merge (DataType tc k _) (RenamingType tc' k' nc)
    | tc == tc' && k == k' = Just (RenamingType tc k nc)
  merge l@(RenamingType tc k _) (DataType tc' k' _)
    | tc == tc' && k == k' = Just l
  merge l@(RenamingType tc k _) (RenamingType tc' k' _)
    | tc == tc' && k == k' = Just l
  merge l@(AliasType tc k _ _) (AliasType tc' k' _ _)
    | tc == tc' && k == k' = Just l
  merge (TypeClass cls k ms) (TypeClass cls' k' ms')
    | cls == cls' && k == k' && (null ms || null ms' || ms == ms') =
    Just $ TypeClass cls k $ if null ms then ms' else ms
  merge _ _ = Nothing

instance Pretty TypeInfo where
  pPrint (DataType qid k cs)    =      text "data" <+> pPrint qid
                                   <>  text "/" <> pPrint k
                                   <+> equals
                                   <+> hsep (punctuate (text "|") (map pPrint cs))
  pPrint (RenamingType qid k c) =      text "newtype" <+> pPrint qid
                                   <>  text "/" <> pPrint k
                                   <+> equals <+> pPrint c
  pPrint (AliasType qid k ar ty)=      text "type" <+> pPrint qid
                                   <>  text "/" <> pPrint k <> text "/" <> int ar
                                   <+> equals <+> pPrint ty
  pPrint (TypeClass qid k ms)   =      text "class" <+> pPrint qid
                                   <>  text "/" <> pPrint k
                                   <+> equals
                                   <+> vcat (blankLine : map pPrint ms)
  pPrint (TypeVar _)            =
    internalError $ "Env.TypeConstructor.Pretty.TypeInfo.pPrint: type variable"

tcKind :: ModuleIdent -> QualIdent -> TCEnv -> Kind
tcKind m tc tcEnv = case qualLookupTypeInfo tc tcEnv of
  [DataType     _ k   _] -> k
  [RenamingType _ k   _] -> k
  [AliasType    _ k _ _] -> k
  _ -> case qualLookupTypeInfo (qualQualify m tc) tcEnv of
    [DataType     _ k   _] -> k
    [RenamingType _ k   _] -> k
    [AliasType    _ k _ _] -> k
    _ -> internalError $
           "Env.TypeConstructor.tcKind: no type constructor: " ++ show tc

clsKind :: ModuleIdent -> QualIdent -> TCEnv -> Kind
clsKind m cls tcEnv = case qualLookupTypeInfo cls tcEnv of
  [TypeClass _ k _] -> k
  _ -> case qualLookupTypeInfo (qualQualify m cls) tcEnv of
    [TypeClass _ k _] -> k
    _ -> internalError $
           "Env.TypeConstructor.clsKind: no type class: " ++ show cls

varKind :: Ident -> TCEnv -> Kind
varKind tv tcEnv
  | isAnonId tv = KindStar
  | otherwise = case lookupTypeInfo tv tcEnv of
    [TypeVar k] -> k
    _ -> internalError "Env.TypeConstructor.varKind: no type variable"

clsMethods :: ModuleIdent -> QualIdent -> TCEnv -> [QualIdent]
clsMethods m cls tcEnv = case qualLookupTypeInfo cls tcEnv of
  [TypeClass _ _ ms] -> map methodName ms
  _ -> case qualLookupTypeInfo (qualQualify m cls) tcEnv of
    [TypeClass _ _ ms] -> map methodName ms
    _ -> internalError $ "Env.TypeConstructor.clsMethods: " ++ show cls

-- Types can only be defined on the top-level; no nested environments are
-- needed for them. Tuple types must be handled as a special case because
-- there is an infinite number of potential tuple types making it
-- impossible to insert them into the environment in advance.

type TCEnv = TopEnv TypeInfo

initTCEnv :: TCEnv
initTCEnv = foldr (uncurry $ predefTC . unapplyType False) emptyTopEnv predefTypes
  where
    predefTC (TypeConstructor tc, tys) =
      predefTopEnv tc . DataType tc (simpleKind $ length tys)
    predefTC _                        =
      internalError "Env.TypeConstructor.initTCEnv.predefTC: no type constructor"

bindTypeInfo :: ModuleIdent -> Ident -> TypeInfo -> TCEnv -> TCEnv
bindTypeInfo m ident ti = bindTopEnv ident ti . qualBindTopEnv qident ti
  where
    qident = qualifyWith m ident

rebindTypeInfo :: ModuleIdent -> Ident -> TypeInfo -> TCEnv -> TCEnv
rebindTypeInfo m ident ti = rebindTopEnv ident ti . qualRebindTopEnv qident ti
  where
    qident = qualifyWith m ident

lookupTypeInfo :: Ident -> TCEnv -> [TypeInfo]
lookupTypeInfo ident tcEnv = lookupTopEnv ident tcEnv ++! lookupTupleTC ident

qualLookupTypeInfo :: QualIdent -> TCEnv -> [TypeInfo]
qualLookupTypeInfo ident tcEnv =
  qualLookupTopEnv ident tcEnv ++! lookupTupleTC (unqualify ident)

qualLookupTypeInfoUnique :: ModuleIdent -> QualIdent -> TCEnv -> [TypeInfo]
qualLookupTypeInfoUnique m qident tcEnv =
  case qualLookupTypeInfo qident tcEnv of
    []   -> []
    [ti] -> [ti]
    tis  -> case qualLookupTypeInfo (qualQualify m qident) tcEnv of
      []  -> tis
      [ti] -> [ti]
      tis' -> tis'

getOrigName :: ModuleIdent -> QualIdent -> TCEnv -> QualIdent
getOrigName m tc tcEnv = case qualLookupTypeInfo tc tcEnv of
  [y] -> origName y
  _ -> case qualLookupTypeInfo (qualQualify m tc) tcEnv of
    [y] -> origName y
    _ -> internalError $ "Env.TypeConstructor.getOrigName: " ++ show tc

reverseLookupByOrigName :: QualIdent -> TCEnv -> [QualIdent]
reverseLookupByOrigName on
  | isQTupleId on = const [on]
  | otherwise     = map fst . filter ((== on) . origName . snd) . allBindings

lookupTupleTC :: Ident -> [TypeInfo]
lookupTupleTC tc | isTupleId tc = [tupleTCs !! (tupleArity tc - 2)]
                 | otherwise    = []

tupleTCs :: [TypeInfo]
tupleTCs = map typeInfo tupleData
  where
    typeInfo dc@(DataConstr _ tys) =
      let n = length tys in DataType (qTupleId n) (simpleKind n) [dc]
    typeInfo (RecordConstr  _ _ _) =
      internalError "Env.TypeConstructor.tupleTCs: record constructor"
