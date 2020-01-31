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

module IL.Typing (Typeable(..), prenexType) where

import Base.Messages (internalError)

import IL.Type

-- | Converts the given type into prenex form.
prenexType :: Type -> Type
prenexType (TypeConstructor tc tys) = TypeConstructor tc $ map prenexType tys
prenexType tv@(TypeVariable _)      = tv
prenexType (TypeArrow ty1 ty2)      = case prenexType ty2 of
  TypeForall tvs ty2' -> TypeForall tvs $ TypeArrow (prenexType ty1) ty2'
  ty2'                -> TypeArrow (prenexType ty1) ty2'
prenexType (TypeForall tvs ty)      = case prenexType ty of
  TypeForall tvs' ty' -> TypeForall (tvs ++ tvs') ty'
  ty'                 -> TypeForall tvs ty'

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
  typeOf (Apply e _) = case instType (typeOf e) of
    TypeArrow _ ty -> ty
    _              -> internalError "IL.Typing.typeOf: application"
    where
      instType (TypeForall _ ty) = instType ty
      instType ty                = ty
  typeOf (Case _ _ as) = typeOf $ head as
  typeOf (Or e _) = typeOf e
  typeOf (Exist _ _ e) = typeOf e
  typeOf (Let _ e) = typeOf e
  typeOf (Letrec _ e) = typeOf e
  typeOf (Typed e _) = typeOf e

instance Typeable Alt where
  typeOf (Alt _ e) = typeOf e
