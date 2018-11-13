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
  nt (Module spi ps m es is ds) = Module spi ps m es is <$> mapM nt ds

instance Show a => Newtypes (Decl a) where
  nt d@(InfixDecl       _ _ _ _) = return d
  nt d@(DataDecl      _ _ _ _ _) = return d
  nt d@(ExternalDataDecl  _ _ _) = return d
  nt (NewtypeDecl p tc vs nc []) = return $ TypeDecl p tc vs $ nconstrType nc
  nt d@(TypeDecl        _ _ _ _) = return d
  nt (FunctionDecl    p a f eqs) = FunctionDecl p a f <$> nt eqs
  nt d@(ExternalDecl        _ _) = return d
  nt (PatternDecl       p t rhs) = PatternDecl p <$> nt t <*> nt rhs
  nt d@(FreeDecl            _ _) = return d
  nt d                           = internalError $
    "Newtypes.Newtypes.nt: unexpected declaration: " ++ show d

instance Show a => Newtypes (Equation a) where
  nt (Equation p lhs rhs) = Equation p <$> nt lhs <*> nt rhs

instance Show a => Newtypes (Lhs a) where
  nt (FunLhs spi f ts) = FunLhs spi f <$> nt ts
  nt lhs           = internalError $
    "Newtypes.Newtypes.nt: unexpected left-hand-side: " ++ show lhs

instance Show a => Newtypes (Rhs a) where
  nt (SimpleRhs p e []) = flip (SimpleRhs p) [] <$> nt e
  nt rhs                = internalError $
    "Newtypes.Newtypes.nt: unexpected right-hand-side: " ++ show rhs

instance Show a => Newtypes (Pattern a) where
  nt t@(LiteralPattern        _ _ _) = return t
  nt t@(VariablePattern       _ _ _) = return t
  nt (ConstructorPattern spi a c ts) = case ts of
    [t] -> do
      isNc <- isNewtypeConstr c
      if isNc then nt t
              else ConstructorPattern spi a c <$> ((: []) <$> nt t)
    _   -> ConstructorPattern spi a c <$> mapM nt ts
  nt (AsPattern             spi v t) = AsPattern spi v <$> nt t
  nt t                               = internalError $
    "Newtypes.Newtypes.nt: unexpected pattern: " ++ show t

instance Show a => Newtypes (Expression a) where
  nt e@(Literal   _   _ _) = return e
  nt e@(Variable    _ _ _) = return e
  nt (Constructor spi a c) = do
    isNc <- isNewtypeConstr c
    return $ if isNc then Variable spi a qIdId else Constructor spi a c
  nt (Apply     spi e1 e2) = case e1 of
    Constructor _ _ c -> do
      isNc <- isNewtypeConstr c
      if isNc then nt e2 else Apply spi <$> nt e1 <*> nt e2
    _ -> Apply spi <$> nt e1 <*> nt e2
  nt (Case    spi ct e as) = Case spi ct <$> nt e <*> mapM nt as
  nt (Let        spi ds e) = Let spi <$> nt ds <*> nt e
  nt (Typed     spi e qty) = flip (Typed spi) qty <$> nt e
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
