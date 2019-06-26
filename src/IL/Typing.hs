{- |
    Module      :  $Header$
    Description :  TODO
    Copyright   :  (c)        2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   TODO
-}

module IL.Typing (Typeable(..)) where

import Base.Messages (internalError)

import IL.Type

class Typeable a where
  typeOf :: a -> Type

instance Typeable ConstrTerm where
  typeOf (LiteralPattern ty _) = ty
  typeOf (ConstructorPattern ty _ _) = ty
  typeOf (VariablePattern ty _) = ty

instance Typeable Expression where
  typeOf (Literal ty _) = ty
  typeOf (Variable ty _) = ty
  typeOf (Function ty _ _) = ty
  typeOf (Constructor ty _ _) = ty
  typeOf (Apply e _) = case typeOf e of
    TypeForall _ (TypeArrow _ ty) -> ty
    TypeArrow _ ty                -> ty
    _ -> internalError "IL.Typing.typeOf: application"
  typeOf (Case _ _ as) = typeOf $ head as
  typeOf (Or e _) = typeOf e
  typeOf (Exist _ _ e) = typeOf e
  typeOf (Let _ e) = typeOf e
  typeOf (Letrec _ e) = typeOf e
  typeOf (Typed e _) = typeOf e

instance Typeable Alt where
  typeOf (Alt _ e) = typeOf e
