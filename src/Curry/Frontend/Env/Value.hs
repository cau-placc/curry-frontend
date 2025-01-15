{- |
    Module      :  $Header$
    Description :  Environment for functions, constructors and labels
    Copyright   :  (c) 2001 - 2004 Wolfgang Lux
                       2011        Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    In order to test the type correctness of a module, the compiler needs
    to determine the type of every data constructor, function and
    variable in the module.
    For the purpose of type checking there is no
    need for distinguishing between variables and functions. For all objects
    their original names and their types are saved. In addition, the compiler
    also saves the (optional) list of field labels for data and newtype
    constructors. Data constructors and functions also contain arity
    information. On import two values are considered equal if their original
    names match.
-}
module Curry.Frontend.Env.Value
  ( ValueEnv, ValueInfo (..)
  , bindGlobalInfo, bindFun, qualBindFun, rebindFun, unbindFun
  , lookupValue, qualLookupValue, qualLookupValueUnique, initDCEnv 
  , ValueType (..), bindLocalVars, bindLocalVar
  , Visibility(..), toVisible, isVisible
  ) where

import Prelude hiding ((<>))
import Control.Monad (zipWithM)

import Curry.Base.Ident
import Curry.Base.Pretty (Pretty(..))

import Curry.Frontend.Base.Messages (internalError)
import Curry.Frontend.Base.TopEnv
import Curry.Frontend.Base.Types
import Curry.Frontend.Base.Utils ((++!))

import Text.PrettyPrint

-- Used to distinguish between imported and hidden class methods. 
data Visibility = Visible | Hidden
  deriving (Eq, Show)

data ValueInfo
  -- |Data constructor with original name, arity, list of record labels and type
  = DataConstructor    QualIdent                   Int [Ident] TypeScheme
  -- |Newtype constructor with original name, record label and type
  -- (arity is always 1)
  | NewtypeConstructor QualIdent                       Ident   TypeScheme
  -- |Value with original name, class method name plus visibility flag, arity and type
  | Value              QualIdent (Maybe (Visibility, QualIdent)) Int         TypeScheme
  -- |Record label with original name, list of constructors for which label
  -- is a valid field and type (arity is always 1)
  | Label              QualIdent [QualIdent]                   TypeScheme
    deriving Show

instance Entity ValueInfo where
  origName (DataConstructor    orgName _ _ _) = orgName
  origName (NewtypeConstructor orgName   _ _) = orgName
  origName (Value              orgName _ _ _) = orgName
  origName (Label              orgName   _ _) = orgName

  merge (DataConstructor c1 ar1 ls1 ty1) (DataConstructor c2 ar2 ls2 ty2)
    | c1 == c2 && ar1 == ar2 && ty1 == ty2 = do
      ls' <- zipWithM mergeLabel ls1 ls2
      Just (DataConstructor c1 ar1 ls' ty1)
  merge (NewtypeConstructor c1 l1 ty1) (NewtypeConstructor c2 l2 ty2)
    | c1 == c2 && ty1 == ty2 = do
      l' <- mergeLabel l1 l2
      Just (NewtypeConstructor c1 l' ty1)
  merge (Value x1 ar1 cm1 ty1) (Value x2 ar2 cm2 ty2)
    | x1 == x2 && ar1 == ar2 && cm1 == cm2 && ty1 == ty2 =
      Just (Value x1 ar1 cm1 ty1)
  merge (Label l1 cs1 ty1) (Label l2 cs2 ty2)
    | l1 == l2 && cs1 == cs2 && ty1 == ty2 = Just (Label l1 cs1 ty1)
  merge _ _ = Nothing

instance Pretty ValueInfo where
  pPrint (DataConstructor qid ar _ tySc) =     text "data" <+> pPrint qid
                                           <>  text "/" <> int ar
                                           <+> equals <+> pPrint tySc
  pPrint (NewtypeConstructor qid _ tySc) =     text "newtype" <+> pPrint qid
                                           <+> equals <+> pPrint tySc
  pPrint (Value qid _ ar tySc)           =     pPrint qid
                                           <>  text "/" <> int ar
                                           <+> equals <+> pPrint tySc
  pPrint (Label qid _ tySc)              =     text "label" <+> pPrint qid
                                           <+> equals <+> pPrint tySc

mergeLabel :: Ident -> Ident -> Maybe Ident
mergeLabel l1 l2
  | l1 == anonId = Just l2
  | l2 == anonId = Just l1
  | l1 == l2     = Just l1
  | otherwise    = Nothing

-- Even though value declarations may be nested, the compiler uses only
-- flat environments for saving type information. This is possible
-- because all identifiers are renamed by the compiler. Here we need
-- special cases for handling tuple constructors.
--
-- Note: the function 'qualLookupValue' has been extended to
-- allow the usage of the qualified list constructor (Prelude.:).

type ValueEnv = TopEnv ValueInfo

bindGlobalInfo :: (QualIdent -> a -> ValueInfo) -> ModuleIdent -> Ident -> a
               -> ValueEnv -> ValueEnv
bindGlobalInfo f m c ty = bindTopEnv c v . qualBindTopEnv qc v
  where qc = qualifyWith m c
        v  = f qc ty

bindFun :: ModuleIdent -> Ident -> Maybe (Visibility, QualIdent) -> Int -> TypeScheme
        -> ValueEnv -> ValueEnv
bindFun m f cm a ty
  | hasGlobalScope f = bindTopEnv f v . qualBindTopEnv qf v
  | otherwise        = bindTopEnv f v
  where qf = qualifyWith m f
        v  = Value qf cm a ty

qualBindFun :: ModuleIdent -> Ident -> Maybe (Visibility, QualIdent) -> Int -> TypeScheme
            -> ValueEnv -> ValueEnv
qualBindFun m f cm a ty = qualBindTopEnv qf $ Value qf cm a ty
  where qf = qualifyWith m f

rebindFun :: ModuleIdent -> Ident -> Maybe (Visibility, QualIdent) -> Int -> TypeScheme
          -> ValueEnv -> ValueEnv
rebindFun m f cm a ty
  | hasGlobalScope f = rebindTopEnv f v . qualRebindTopEnv qf v
  | otherwise        = rebindTopEnv f v
  where qf = qualifyWith m f
        v  = Value qf cm a ty

unbindFun :: Ident -> ValueEnv -> ValueEnv
unbindFun = unbindTopEnv

lookupValue :: Ident -> ValueEnv -> [ValueInfo]
lookupValue x tyEnv = lookupTopEnv x tyEnv ++! lookupTuple x

qualLookupValue :: QualIdent -> ValueEnv -> [ValueInfo]
qualLookupValue x tyEnv = qualLookupTopEnv x tyEnv
                      ++! lookupTuple (unqualify x)

qualLookupValueUnique :: ModuleIdent -> QualIdent -> ValueEnv -> [ValueInfo]
qualLookupValueUnique m x tyEnv = case qualLookupValue x tyEnv of
  []  -> []
  [v] -> [v]
  vs  -> case qualLookupValue (qualQualify m x) tyEnv of
    []  -> vs
    [v] -> [v]
    qvs -> qvs

lookupTuple :: Ident -> [ValueInfo]
lookupTuple c | isTupleId c = [tupleDCs !! (tupleArity c - 2)]
              | otherwise   = []

tupleDCs :: [ValueInfo]
tupleDCs = map dataInfo tupleData
  where dataInfo (DataConstr _ tys) =
          let n = length tys
          in  DataConstructor (qTupleId n) n (replicate n anonId) $
                ForAll n $ predType $ foldr TypeArrow (tupleType tys) tys
        dataInfo RecordConstr {}    =
          internalError $ "Env.Value.tupleDCs: " ++ show tupleDCs

-- Since all predefined types are free of existentially quantified type
-- variables and have an empty predicate set, we can ignore both of them
-- when entering the types into the value environment.

initDCEnv :: ValueEnv
initDCEnv = foldr predefDC emptyTopEnv
  [ (c, length tys, constrType (polyType ty) tys)
  | (ty, cs) <- predefTypes, DataConstr c tys <- cs ]
  where predefDC (c, a, ty) = predefTopEnv c' (DataConstructor c' a ls ty)
          where ls = replicate a anonId
                c' = qualify c
        constrType (ForAll n (PredType ps ty)) =
          ForAll n . PredType ps . foldr TypeArrow ty

-- The functions 'bindLocalVar' and 'bindLocalVars' add the type of one or
-- many local variables or functions to the value environment. In contrast
-- to global functions, we do not care about the name of the module containing
-- the variable or function's definition.

class ValueType t where
  toValueType :: Type -> t
  fromValueType :: t -> PredType

instance ValueType Type where
  toValueType = id
  fromValueType = predType

instance ValueType PredType where
  toValueType = predType
  fromValueType = id

bindLocalVars :: ValueType t => [(Ident, Int, t)] -> ValueEnv -> ValueEnv
bindLocalVars = flip $ foldr bindLocalVar

bindLocalVar :: ValueType t => (Ident, Int, t) -> ValueEnv -> ValueEnv
bindLocalVar (v, a, ty) =
  bindTopEnv v $ Value (qualify v) Nothing a $ typeScheme $ fromValueType ty

--- Converts a `Bool` to a `Visibility` entity.
toVisible :: Bool -> Visibility
toVisible True  = Visible
toVisible False = Hidden

--- Converts a `Visibility` entity to a `Bool`.
isVisible :: Visibility -> Bool
isVisible Visible = True
isVisible Hidden  = False