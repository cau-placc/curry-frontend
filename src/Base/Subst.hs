{- |
    Module      :  $Header$
    Description :  General substitution implementation
    Copyright   :  (c) 2002 Wolfgang Lux
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The module Subst implements substitutions. A substitution
   sigma = {x_1 |-> t_1, ... ,x_n |-> t_n} is a finite mapping from
   (finitely many) variables x_1, ... ,x_n to some kind of expression
   or term.

   In order to implement substitutions efficiently,
   composed substitutions are marked with a boolean flag (see below).
-}

module Base.Subst
  ( Subst (..), IntSubst (..), idSubst, singleSubst, bindSubst, unbindSubst
  , substToList, compose, lookupSubst, substVar', isubstVar, restrictSubstTo
  ) where

import qualified Data.Map as Map

-- |Data type for substitution
data Subst a b = Subst Bool (Map.Map a b)
  deriving Show

-- |Identity substitution
idSubst :: Subst a b
idSubst = Subst False Map.empty

-- |Convert a substitution to a list of replacements
substToList :: Subst v e -> [(v, e)]
substToList (Subst _ sigma) = Map.toList sigma

-- |Create a substitution for a single replacement
singleSubst :: Ord v => v -> e -> Subst v e
singleSubst v e = bindSubst v e idSubst

-- |Extend a substitution with a single replacement
bindSubst :: Ord v => v -> e -> Subst v e -> Subst v e
bindSubst v e (Subst comp sigma) = Subst comp $ Map.insert v e sigma

-- |Remove a single replacement from a substitution
unbindSubst :: Ord v => v -> Subst v e -> Subst v e
unbindSubst v (Subst comp sigma) = Subst comp $ Map.delete v sigma

lookupSubst :: Ord v => v -> Subst v e -> Maybe e
lookupSubst v (Subst _ sigma) = Map.lookup v sigma

-- For any substitution we have the following definitions:
--     sigma(x)     = t_i   if x = x_i
--                    x    otherwise
--     Dom(sigma)   = {x_1, ... , x_n}
--     Codom(sigma) = {t_1, ... , t_n}
-- Note that obviously the set of variables must be a subset of the set
-- of expressions. Also it is usually possible to extend the substitution
-- to a homomorphism on the codomain of the substitution. This is
-- captured by the following class declaration:

-- class Ord v => Subst v e where
--   var :: v -> e
--   subst :: Subst v e -> e -> e

-- With the help of the injection 'var', we can then compute the
-- substitution for a variable sigma(v) and also the composition of
-- two substitutions sigma1 o sigma2(e) := sigma1(sigma2(e)).
-- A naive implementation of the composition were
--
--   compose sigma sigma' =
--     foldr (uncurry bindSubst) sigma (substToList (fmap (subst sigma) sigma'))
--
-- However, such an implementation is very inefficient because the
-- number of substiutions applied to a variable increases in
-- O(n) of the number of compositions.

-- A more efficient implementation is to apply 'subst' again to
-- the value substituted for a variable in Dom(sigma).
-- However, this is correct only as long as the result of the substitution
-- does not include any variables which are in Dom(sigma). For instance,
-- it is impossible to implement simple variable renamings in this way.

-- Therefore we use the simple strategy to apply 'subst' again
-- only in case of a substitution which was returned from 'compose'.

-- substVar :: Subst v e => Subst v e -> v -> e
-- substVar (Subst comp sigma) v = maybe (var v) subst' (Map.lookup v sigma)
--   where subst' = if comp then subst (Subst comp sigma) else id

-- |Compose two substitutions
compose :: Ord v => Subst v e -> Subst v e -> Subst v e
compose sigma sigma' =
  composed (foldr (uncurry bindSubst) sigma' (substToList sigma))
  where composed (Subst _ sigma'') = Subst True sigma''

-- Unfortunately Haskell does not (yet) support multi-parameter type
-- classes. For that reason we have to define a separate class for each
-- kind of variable type for these functions. We implement
-- 'substVar' as a function that takes the class functions as an
-- additional parameters. As an example for the use of this function the
-- module includes a class 'IntSubst' for substitution whose
-- domain are integer numbers.

-- |Apply a substitution to a variable
substVar' :: Ord v => (v -> e) -> (Subst v e -> e -> e)
          -> Subst v e -> v -> e
substVar' var subst (Subst comp sigma) v =
  maybe (var v) subst' (Map.lookup v sigma)
  where subst' = if comp then subst (Subst comp sigma) else id

-- |Type class for terms where variables are represented as 'Int's
class IntSubst e where
  -- |Construct a variable from an 'Int'
  ivar :: Int -> e
  -- |Apply a substitution to a term
  isubst :: Subst Int e -> e -> e

-- |Apply a substitution to a term with variables represented as 'Int's
isubstVar :: IntSubst e => Subst Int e -> Int -> e
isubstVar = substVar' ivar isubst

-- |The function 'restrictSubstTo' implements the restriction of a
-- substitution to a given subset of its domain.
restrictSubstTo :: Ord v => [v] -> Subst v e -> Subst v e
restrictSubstTo vs (Subst comp sigma) =
  foldr (uncurry bindSubst) (Subst comp Map.empty)
        (filter ((`elem` vs) . fst) (Map.toList sigma))
