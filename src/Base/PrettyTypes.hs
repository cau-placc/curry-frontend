{- |
    Module      :  $Header$
    Description :  TODO
    Copyright   :  (c) 2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   TODO
-}
{-# LANGUAGE CPP #-}
module Base.PrettyTypes where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import Data.Maybe (fromMaybe)
import qualified Data.Set as Set (Set, toAscList)

import Curry.Base.Ident (identSupply)
import Curry.Base.Pretty
import Curry.Syntax.Pretty

import Base.CurryTypes
import Base.Types

instance Pretty Type where
  pPrint = ppTypeExpr 0 . fromType identSupply

instance Pretty Pred where
  pPrint = ppConstraint . fromPred identSupply

instance Pretty a => Pretty (Set.Set a) where
  pPrint = parens . list . map pPrint . Set.toAscList

instance Pretty PredType where
  pPrint = ppQualTypeExpr . fromPredType identSupply

instance Pretty DataConstr where
  pPrint (DataConstr i _ tys)      = pPrint i <+> hsep (map pPrint tys)
  pPrint (RecordConstr i _ ls tys) =     pPrint i
                                     <+> braces (hsep (punctuate comma pLs))
    where
      pLs = zipWith (\l ty -> pPrint l <+> colon <> colon <+> pPrint ty) ls tys

instance Pretty ClassMethod where
  pPrint (ClassMethod f mar pty) =     pPrint f
                                   <>  text "/" <> int (fromMaybe 0 mar)
                                   <+> colon <> colon <+> pPrint pty

instance Pretty TypeScheme where
  pPrint (ForAll _ ty) = pPrint ty
