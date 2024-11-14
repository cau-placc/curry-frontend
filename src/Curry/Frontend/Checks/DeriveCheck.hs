{- |
    Module      :  $Header$
    Description :  Checks deriving clauses
    Copyright   :  (c)        2016 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   Before entering derived instances into the instance environment, the
   compiler has to ensure that it is not asked for other instances than
   those of supported type classes.
-}
module Checks.DeriveCheck (deriveCheck) where

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Base.SpanInfo (HasSpanInfo)
import Curry.Syntax

import Base.Messages (Message, spanInfoMessage)

import Env.TypeConstructor

deriveCheck :: TCEnv -> Module a -> [Message]
deriveCheck tcEnv (Module _ _ _ m _ _ ds) = concatMap (checkDecl m tcEnv) ds

-- No instances can be derived for abstract data types as well as for
-- existential data types.

checkDecl :: ModuleIdent -> TCEnv -> Decl a -> [Message]
checkDecl m tcEnv (DataDecl   _ tc _ cs clss)
  | null clss                       = []
  | null cs                         = [errNoAbstractDerive tc]
  | otherwise                       = concatMap (checkDerivable m tcEnv cs) clss
checkDecl m tcEnv (NewtypeDecl _ _ _ nc clss) =
  concatMap (checkDerivable m tcEnv [toConstrDecl nc]) clss
checkDecl _ _     _                           = []

checkDerivable :: ModuleIdent -> TCEnv -> [ConstrDecl] -> QualIdent -> [Message]
checkDerivable m tcEnv cs cls
  | ocls == qEnumId && not (isEnum cs)       = [errNotEnum cls]
  | ocls == qBoundedId && not (isBounded cs) = [errNotBounded cls]
  | ocls `notElem` derivableClasses          = [errNotDerivable cls]
  | ocls == qDataId                          = [errNoDataDerive cls]
  | otherwise                                = []
  where ocls = getOrigName m cls tcEnv

derivableClasses :: [QualIdent]
derivableClasses = [qEqId, qOrdId, qEnumId, qBoundedId, qReadId, qShowId, qDataId]

-- Instances of 'Enum' can be derived only for enumeration types, i.e., types
-- where all data constructors are constants.

isEnum :: [ConstrDecl] -> Bool
isEnum = all ((0 ==) . constrArity)

-- Instances of 'Bounded' can be derived only for enumerations and for single
-- constructor types.

isBounded :: [ConstrDecl] -> Bool
isBounded cs = length cs == 1 || isEnum cs

-- ---------------------------------------------------------------------------
-- Auxiliary functions
-- ---------------------------------------------------------------------------

toConstrDecl :: NewConstrDecl -> ConstrDecl
toConstrDecl (NewConstrDecl p c      ty) = ConstrDecl p c [ty]
toConstrDecl (NewRecordDecl p c (l, ty)) =
  RecordDecl p c [FieldDecl p [l] ty]

constrArity :: ConstrDecl -> Int
constrArity (ConstrDecl  _ _ tys) = length tys
constrArity (ConOpDecl   _ _ _ _) = 2
constrArity c@(RecordDecl  _ _ _) = length $ recordLabels c

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errNoAbstractDerive :: HasSpanInfo a => a -> Message
errNoAbstractDerive s = spanInfoMessage s $
  text "Instances can only be derived for data types with" <+>
  text "at least one constructor"

errNotDerivable :: QualIdent -> Message
errNotDerivable cls = spanInfoMessage cls $ hsep $ map text
  ["Instances of type class", escQualName cls, "cannot be derived"]

errNoDataDerive :: QualIdent -> Message
errNoDataDerive qcls = spanInfoMessage qcls $ hsep $ map text
  [ "Instances of type class"
  , escQualName qcls
  , "are automatically derived if possible"
  ]

errNotEnum :: QualIdent -> Message
errNotEnum qcls = spanInfoMessage qcls $ hsep $ map text
  [ "Instances of type class"
  , escQualName qcls
  , "can be derived only for enumeration types"
  ]

errNotBounded :: QualIdent -> Message
errNotBounded qcls = spanInfoMessage qcls $ hsep $ map text
  [ "Instances of type class"
  , escQualName qcls
  , "can be derived only for enumeration and single constructor types"
  ]
