{- |
    Module      :  $Header$
    Description :  Environment of type constructors
    Copyright   :  (c) 2002 - 2004, Wolfgang Lux
                       2011       , Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    For all defined types the compiler must maintain kind information. At
    present, Curry does not support type classes. Therefore its type
    language is first order and the only information that must be recorded
    is the arity of each type. For algebraic data types and renaming types
    the compiler also records all data constructors belonging to that
    type, for alias types the type expression to be expanded is saved. In
    order to manage the import and export of types, the names of the
    original definitions are also recorded. On import two types are
    considered equal if their original names match.

    The information for a data constructor comprises the number of
    existentially quantified type variables and the list of the argument
    types. Note that renaming type constructors have only one type
    argument.

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
  ( TCEnv, TypeInfo (..), initTCEnv, tcArity, bindTypeInfo
  , lookupTC, qualLookupTC, qualLookupTCUnique
  , TypeEnv, TypeKind (..), typeKind
  ) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import Curry.Base.Ident
import Curry.Base.Pretty (Pretty(..))

import Base.Messages     (internalError)
import Base.TopEnv
import Base.Types
import Base.Utils         ((++!))

import Text.PrettyPrint

data TypeInfo
  = DataType     QualIdent Int [DataConstr]
  | RenamingType QualIdent Int DataConstr
  | AliasType    QualIdent Int Type
    deriving Show

instance Entity TypeInfo where
  origName (DataType     tc _ _) = tc
  origName (RenamingType tc _ _) = tc
  origName (AliasType    tc _ _) = tc

  merge (DataType tc n cs) (DataType tc' _ cs')
    | tc == tc' && (null cs || null cs' || cs == cs') =
        Just $ DataType tc n (if null cs then cs' else cs)
  merge (DataType tc n _) (RenamingType tc' _ nc)
    | tc == tc' = Just (RenamingType tc n nc)
  merge l@(RenamingType tc _ _) (DataType tc' _ _)
    | tc == tc' = Just l
  merge l@(RenamingType tc _ _) (RenamingType tc' _ _)
    | tc == tc' = Just l
  merge l@(AliasType tc _ _) (AliasType tc' _ _)
    | tc == tc' = Just l
  merge _ _ = Nothing

instance Pretty TypeInfo where
  pPrint (DataType qid ar cs)    =     text "data" <+> pPrint qid
                                   <>  text "/" <> int ar
                                   <+> equals
                                   <+> hsep (punctuate (text "|") (map pPrint cs))
  pPrint (RenamingType qid ar c) =     text "newtype" <+> pPrint qid
                                   <>  text "/" <> int ar
                                   <+> equals <+> pPrint c
  pPrint (AliasType qid ar ty)   =     text "type" <+> pPrint qid
                                   <>  text "/" <> int ar
                                   <+> equals <+> pPrint ty

tcArity :: TypeInfo -> Int
tcArity (DataType     _ n _) = n
tcArity (RenamingType _ n _) = n
tcArity (AliasType    _ n _) = n

-- Types can only be defined on the top-level; no nested environments are
-- needed for them. Tuple types must be handled as a special case because
-- there is an infinite number of potential tuple types making it
-- impossible to insert them into the environment in advance.

type TCEnv = TopEnv TypeInfo

bindTypeInfo :: (QualIdent -> Int -> a -> TypeInfo) -> ModuleIdent
             -> Ident -> [Ident] -> a -> TCEnv -> TCEnv
bindTypeInfo f m tc tvs x = bindTopEnv tc ty . qualBindTopEnv qtc ty
  where qtc = qualifyWith m tc
        ty  = f qtc (length tvs) x

lookupTC :: Ident -> TCEnv -> [TypeInfo]
lookupTC tc tcEnv = lookupTopEnv tc tcEnv ++! lookupTupleTC tc

qualLookupTC :: QualIdent -> TCEnv -> [TypeInfo]
qualLookupTC tc tcEnv = qualLookupTopEnv tc tcEnv
                    ++! lookupTupleTC (unqualify tc)

qualLookupTCUnique :: ModuleIdent -> QualIdent -> TCEnv -> [TypeInfo]
qualLookupTCUnique m x tyEnv = case qualLookupTC x tyEnv of
  []  -> []
  [t] -> [t]
  ts  -> case qualLookupTC (qualQualify m x) tyEnv of
    []  -> ts
    [t] -> [t]
    qts -> qts

lookupTupleTC :: Ident -> [TypeInfo]
lookupTupleTC tc | isTupleId tc = [tupleTCs !! (tupleArity tc - 2)]
                 | otherwise    = []

tupleTCs :: [TypeInfo]
tupleTCs = map typeInfo tupleData
  where typeInfo dc@(DataConstr _ n _)  = DataType (qTupleId n) n [dc]
        typeInfo (RecordConstr _ _ _ _) =
          internalError $ "Env.TypeConstructor.tupleTCs: " ++ show tupleData

initTCEnv :: TCEnv
initTCEnv = foldr (uncurry predefTC) emptyTopEnv predefTypes
  where
  predefTC (TypeConstructor tc tys) = predefTopEnv tc
                                    . DataType tc (length tys)
  predefTC _ = internalError "Base.initTCEnv.predefTC: no type constructor"

type TypeEnv = TopEnv TypeKind

data TypeKind
  = Data QualIdent [Ident]
  | Alias QualIdent
  deriving (Eq, Show)

typeKind :: TypeInfo -> TypeKind
typeKind (DataType     tc _ cs) = Data tc (map constrIdent cs)
typeKind (RenamingType tc _ nc) = Data tc [constrIdent nc]
typeKind (AliasType    tc _ _)  = Alias tc

instance Entity TypeKind where
  origName (Data tc _) = tc
  origName (Alias  tc) = tc
