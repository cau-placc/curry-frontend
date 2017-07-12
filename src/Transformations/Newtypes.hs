{- |
  Module      :  $Header$
  Description :  Removing newtype constructors
  Copyright   :  (c) 2017        Finn Teegen
  License     :  BSD-3-clause

  Maintainer  :  fte@informatik.uni-kiel.de
  Stability   :  experimental
  Portability :  portable

  After inserting dictionaries, the compiler removes all occurences of
  newtype declarations. Applications 'N x' in patterns and expressions,
  where 'N' is a newtype constructor, are replaced by a 'x'. The newtype
  declarations are replaced by type synonyms and partial applications of
  newtype constructors are changed into calls to 'Prelude.id'.
-}
{-# LANGUAGE CPP #-}
module Transformations.Newtypes (removeNewtypes) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import qualified Control.Monad.Reader as R

import Curry.Base.Ident
import Curry.Syntax

import Base.Messages (internalError)
import Base.Types

import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

removeNewtypes :: ValueEnv -> Module Type -> Module Type
removeNewtypes vEnv mdl = R.runReader (nt mdl) vEnv

type NTM a = R.Reader ValueEnv a

class Show a => Newtypes a where
  nt :: a -> NTM a

instance Newtypes a => Newtypes [a] where
  nt = mapM nt

instance Show a => Newtypes (Module a) where
  nt (Module ps m es is ds) = Module ps m es is <$> mapM nt ds

instance Show a => Newtypes (Decl a) where
  nt d@(InfixDecl       _ _ _ _) = return d
  nt d@(DataDecl      _ _ _ _ _) = return d
  nt (NewtypeDecl p tc vs nc []) = return $ TypeDecl p tc vs $ nconstrType nc
  nt d@(TypeDecl        _ _ _ _) = return d
  nt (FunctionDecl    p a f eqs) = FunctionDecl p a f <$> nt eqs
  nt d@(ForeignDecl _ _ _ _ _ _) = return d
  nt (PatternDecl       p t rhs) = PatternDecl p <$> nt t <*> nt rhs
  nt d@(FreeDecl            _ _) = return d
  nt d                           = internalError $
    "Newtypes.Newtypes.nt: unexpected declaration: " ++ show d

instance Show a => Newtypes (Equation a) where
  nt (Equation p lhs rhs) = Equation p <$> nt lhs <*> nt rhs

instance Show a => Newtypes (Lhs a) where
  nt (FunLhs f ts) = FunLhs f <$> nt ts
  nt lhs           = internalError $
    "Newtypes.Newtypes.nt: unexpected left-hand-side: " ++ show lhs

instance Show a => Newtypes (Rhs a) where
  nt (SimpleRhs p e []) = flip (SimpleRhs p) [] <$> nt e
  nt rhs                = internalError $
    "Newtypes.Newtypes.nt: unexpected right-hand-side: " ++ show rhs

instance Show a => Newtypes (Pattern a) where
  nt t@(LiteralPattern      _ _) = return t
  nt t@(VariablePattern     _ _) = return t
  nt (ConstructorPattern a c ts) = case ts of
    [t] -> do
      isNc <- isNewtypeConstr c
      if isNc then nt t
              else ConstructorPattern a c <$> ((: []) <$> nt t)
    _   -> ConstructorPattern a c <$> mapM nt ts
  nt (AsPattern             v t) = AsPattern v <$> nt t
  nt t                      = internalError $
    "Newtypes.Newtypes.nt: unexpected pattern: " ++ show t

instance Show a => Newtypes (Expression a) where
  nt e@(Literal   _ _) = return e
  nt e@(Variable  _ _) = return e
  nt (Constructor a c) = do
    isNc <- isNewtypeConstr c
    return $ if isNc then Variable a qIdId else Constructor a c
  nt (Apply     e1 e2) = case e1 of
    Constructor _ c -> do
      isNc <- isNewtypeConstr c
      if isNc then nt e2 else Apply <$> nt e1 <*> nt e2
    _ -> Apply <$> nt e1 <*> nt e2
  nt (Case    ct e as) = Case ct <$> nt e <*> mapM nt as
  nt (Let        ds e) = Let <$> nt ds <*> nt e
  nt (Typed     e qty) = flip Typed qty <$> nt e
  nt e                 = internalError $
    "Newtypes.Newtypes.nt: unexpected expression: " ++ show e

instance Show a => Newtypes (Alt a) where
  nt (Alt p t rhs) = Alt p <$> nt t <*> nt rhs

isNewtypeConstr :: QualIdent -> NTM Bool
isNewtypeConstr c = R.ask >>= \vEnv -> return $
  case qualLookupValue c vEnv of
    [NewtypeConstructor _ _ _] -> True
    [DataConstructor  _ _ _ _] -> False
    _ -> internalError $ "Newtypes.isNewtypeConstr: " ++ show c
