{- |
    Module      :  $Header$
    Description :  Environment for functions, constructors and labels
    Copyright   :  (c) 2001 - 2004, Wolfgang Lux
                       2011       , Björn Peemöller
                       2015       , Jan Tikovsky
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

{-# LANGUAGE CPP #-}
module Env.Value
  ( ValueEnv, ValueInfo (..)
  , bindGlobalInfo, bindFun, qualBindFun, rebindFun, unbindFun
  , lookupValue, qualLookupValue, qualLookupValueUnique
  , initDCEnv, ppTypes
  , conType
  ) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty (Pretty(..))
import Curry.Syntax

import Base.CurryTypes (fromQualType)
import Base.Messages (internalError)
import Base.TopEnv
import Base.Types
import Base.Utils ((++!))

import Text.PrettyPrint

data ValueInfo
  -- |Data constructor with original name, arity, list of record labels and type
  = DataConstructor    QualIdent Int [Ident] ExistTypeScheme
  -- |Newtype constructor with original name, record label and type
  -- (arity is always 1)
  | NewtypeConstructor QualIdent     Ident   ExistTypeScheme
  -- |Value with original name, arity and type
  | Value              QualIdent Int         TypeScheme
  -- |Record label with original name, list of constructors for which label
  -- is valid field and type (arity is always 1)
  | Label              QualIdent [QualIdent] TypeScheme
    deriving Show

instance Entity ValueInfo where
  origName (DataConstructor    orgName _ _ _) = orgName
  origName (NewtypeConstructor orgName   _ _) = orgName
  origName (Value              orgName   _ _) = orgName
  origName (Label              orgName   _ _) = orgName

  merge (DataConstructor c1 ar1 ls1 ty1) (DataConstructor c2 ar2 ls2 ty2)
    | c1 == c2 && ar1 == ar2 && ty1 == ty2 = do
      ls' <- sequence (zipWith mergeLabel ls1 ls2)
      Just (DataConstructor c1 ar1 ls' ty1)
  merge (NewtypeConstructor c1 l1 ty1) (NewtypeConstructor c2 l2 ty2)
    | c1 == c2 && ty1 == ty2 = do
      l' <- mergeLabel l1 l2
      Just (NewtypeConstructor c1 l' ty1)
  merge (Value x1 ar1 ty1) (Value x2 ar2 ty2)
    | x1 == x2 && ar1 == ar2 && ty1 == ty2 = Just (Value x1 ar1 ty1)
  merge (Label l1 cs1 ty1) (Label l2 cs2 ty2)
    | l1 == l2 && cs1 == cs2 && ty1 == ty2 = Just (Label l1 cs1 ty1)
  merge _ _ = Nothing

instance Pretty ValueInfo where
  pPrint (DataConstructor qid ar _ ts)  =     text "data" <+> pPrint qid
                                          <>  text "/" <> int ar
                                          <+> equals <+> pPrint ts
  pPrint (NewtypeConstructor qid _ ts) =     text "newtype" <+> pPrint qid
                                          <+> equals <+> pPrint ts
  pPrint (Value qid ar ts)              =     pPrint qid
                                          <>  text "/" <> int ar
                                          <+> equals <+> pPrint ts
  pPrint (Label qid _ ts)               =     text "label" <+> pPrint qid
                                          <+> equals <+> pPrint ts

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

bindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
bindFun m f a ty
  | hasGlobalScope f = bindTopEnv f v . qualBindTopEnv qf v
  | otherwise        = bindTopEnv f v
  where qf = qualifyWith m f
        v  = Value qf a ty

qualBindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
qualBindFun m f a ty = qualBindTopEnv qf $ Value qf a ty
  where qf = qualifyWith m f

rebindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv
          -> ValueEnv
rebindFun m f a ty
  | hasGlobalScope f = rebindTopEnv f v . qualRebindTopEnv qf v
  | otherwise        = rebindTopEnv f v
  where qf = qualifyWith m f
        v  = Value qf a ty

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
  where dataInfo (DataConstr _ n tys) =
          DataConstructor (qTupleId n) n (replicate n anonId)
            (ForAllExist n 0 $ foldr TypeArrow (tupleType tys) tys)
        dataInfo (RecordConstr _ _ _ _) = internalError $ "Env.Value.tupleDCs: "
                                            ++ show tupleDCs

initDCEnv :: ValueEnv
initDCEnv = foldr predefDC emptyTopEnv
  [ (c, length tys, constrType (polyType ty) n' tys)
  | (ty, cs) <- predefTypes, DataConstr c n' tys <- cs]
  where predefDC (c, a, ty) = predefTopEnv c' (DataConstructor c' a ls ty)
          where ls = replicate a anonId
                c' = qualify c
        constrType (ForAll n ty) n' = ForAllExist n n' . foldr TypeArrow ty

-- |Pretty-printing the types from the type environment
ppTypes :: ModuleIdent -> ValueEnv -> Doc
ppTypes mid valueEnv = ppTypes' mid $ localBindings valueEnv
  where
  ppTypes' :: ModuleIdent -> [(Ident, ValueInfo)] -> Doc
  ppTypes' m = vcat . map (ppIDecl . mkDecl) . filter (isValue . snd)
    where
    mkDecl (v, Value _ a (ForAll _ ty)) =
      IFunctionDecl NoPos (qualify v) a (fromQualType m ty)
    mkDecl _ = internalError "Env.Value.ppTypes: no value"
    isValue (Value _ _ _) = True
    isValue _             = False

conType :: QualIdent -> ValueEnv -> ([Ident], ExistTypeScheme)
conType c tyEnv = case qualLookupTopEnv c tyEnv of
  [DataConstructor _ _ ls ty] -> (ls , ty)
  [NewtypeConstructor _ l ty] -> ([l], ty)
  _                           -> internalError $ "Env.Value.conType: " ++ show c
