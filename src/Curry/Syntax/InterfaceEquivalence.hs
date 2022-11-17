{- |
    Module      :  $Header$
    Description :  Comparison of Curry Interfaces
    Copyright   :  (c) 2000 - 2007 Wolfgang Lux
                       2014 - 2015 Björn Peemöller
                       2014        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    If a module is recompiled, the compiler has to check whether the
    interface file must be updated. This must be done if any exported
    entity has been changed, or an export was removed or added. The
    function 'intfEquiv' checks whether two interfaces are
    equivalent, i.e., whether they define the same entities.
-}
module Curry.Syntax.InterfaceEquivalence (fixInterface, intfEquiv) where

import Data.List (deleteFirstsBy, sort)
import qualified Data.Set as Set

import Curry.Base.Ident
import Curry.Syntax

infix 4 =~=, `eqvSet`

-- |Are two given interfaces equivalent?
intfEquiv :: Interface -> Interface -> Bool
intfEquiv = (=~=)

-- |Type class to express the equivalence of two values
class Equiv a where
  (=~=) :: a -> a -> Bool

instance Equiv a => Equiv (Maybe a) where
  Nothing =~= Nothing = True
  Nothing =~= Just _  = False
  Just _  =~= Nothing = False
  Just x  =~= Just y  = x =~= y

instance Equiv a => Equiv [a] where
  []     =~= []     = True
  (x:xs) =~= (y:ys) = x =~= y && xs =~= ys
  _      =~= _      = False

eqvList, eqvSet :: Equiv a => [a] -> [a] -> Bool
xs `eqvList` ys = length xs == length ys && and (zipWith (=~=) xs ys)
xs `eqvSet` ys = null (deleteFirstsBy (=~=) xs ys ++ deleteFirstsBy (=~=) ys xs)

instance Equiv Interface where
  Interface m1 is1 ds1 =~= Interface m2 is2 ds2
    = m1 == m2 && is1 `eqvSet` is2 && ds1 `eqvSet` ds2

instance Equiv IImportDecl where
  IImportDecl _ m1 =~= IImportDecl _ m2 = m1 == m2

-- Since the kind of type constructors or type classes can be omitted
-- in the interface when the kind is simple, i.e., it is either * or of
-- the form * -> ... -> *, a non given kind has to be considered equivalent
-- to a given one if the latter is simple.

eqvKindExpr :: Maybe KindExpr -> Maybe KindExpr -> Bool
Nothing  `eqvKindExpr` (Just k) = isSimpleKindExpr k
(Just k) `eqvKindExpr` Nothing  = isSimpleKindExpr k
k1       `eqvKindExpr` k2       = k1 == k2

isSimpleKindExpr :: KindExpr -> Bool
isSimpleKindExpr Star               = True
isSimpleKindExpr (ArrowKind Star k) = isSimpleKindExpr k
isSimpleKindExpr _                  = False


instance Equiv IDecl where
  IInfixDecl _ fix1 p1 op1 =~= IInfixDecl _ fix2 p2 op2
    = fix1 == fix2 && p1 == p2 && op1 == op2
  HidingDataDecl _ tc1 k1 tvs1 =~= HidingDataDecl _ tc2 k2 tvs2
    = tc1 == tc2 && k1 `eqvKindExpr` k2 && tvs1 == tvs2
  IDataDecl _ tc1 k1 tvs1 cs1 hs1 =~= IDataDecl _ tc2 k2 tvs2 cs2 hs2
    = tc1 == tc2 && k1 `eqvKindExpr` k2 && tvs1 == tvs2 && cs1 =~= cs2 &&
      hs1 `eqvSet` hs2
  INewtypeDecl _ tc1 k1 tvs1 nc1 hs1 =~= INewtypeDecl _ tc2 k2 tvs2 nc2 hs2
    = tc1 == tc2 && k1 `eqvKindExpr` k2 && tvs1 == tvs2 && nc1 =~= nc2 &&
      hs1 `eqvSet` hs2
  ITypeDecl _ tc1 k1 tvs1 ty1 =~= ITypeDecl _ tc2 k2 tvs2 ty2
    = tc1 == tc2 && k1 `eqvKindExpr` k2 && tvs1 == tvs2 && ty1 == ty2
  IFunctionDecl _ f1 cm1 n1 qty1 =~= IFunctionDecl _ f2 cm2 n2 qty2
    = f1 == f2 && cm1 == cm2 && n1 == n2 && qty1 == qty2
  HidingClassDecl _ cx1 cls1 k1 _ _ =~= HidingClassDecl _ cx2 cls2 k2 _ _
    = cx1 == cx2 && cls1 == cls2 && k1 `eqvKindExpr` k2
  IClassDecl _ cx1 cls1 k1 _ _ ms1 hs1 =~= IClassDecl _ cx2 cls2 k2 _ _ ms2 hs2
    = cx1 == cx2 && cls1 == cls2 && k1 `eqvKindExpr` k2 &&
      ms1 `eqvList` ms2 && hs1 `eqvSet` hs2
  IInstanceDecl _ cx1 cls1 tys1 is1 m1 =~= IInstanceDecl _ cx2 cls2 tys2 is2 m2
    = cx1 == cx2 && cls1 == cls2 && tys1 == tys2 && sort is1 == sort is2 &&
      m1 == m2
  _ =~= _ = False

instance Equiv ConstrDecl where
  ConstrDecl _ c1 tys1 =~= ConstrDecl _ c2 tys2
    = c1 == c2 && tys1 == tys2
  ConOpDecl _ ty11 op1 ty12 =~= ConOpDecl _ ty21 op2 ty22
    = op1 == op2 && ty11 == ty21 && ty12 == ty22
  RecordDecl _ c1 fs1 =~= RecordDecl _ c2 fs2
    = c1 == c2 && fs1 `eqvList` fs2
  _ =~= _ = False

instance Equiv FieldDecl where
  FieldDecl _ ls1 ty1 =~= FieldDecl _ ls2 ty2 = ls1 == ls2 && ty1 == ty2

instance Equiv NewConstrDecl where
  NewConstrDecl _ c1 ty1 =~= NewConstrDecl _ c2 ty2 = c1 == c2 && ty1 == ty2
  NewRecordDecl _ c1 fld1 =~= NewRecordDecl _ c2 fld2 = c1 == c2 && fld1 == fld2
  _ =~= _ = False

instance Equiv IMethodDecl where
  IMethodDecl _ f1 a1 qty1 =~= IMethodDecl _ f2 a2 qty2
    = f1 == f2 && a1 == a2 && qty1 == qty2

instance Equiv Ident where
  (=~=) = (==)

-- If we check for a change in the interface, we do not need to check the
-- interface declarations, but still must disambiguate (nullary) type
-- constructors and type variables in type expressions. This is handled
-- by function 'fixInterface' and the associated type class 'FixInterface'.

-- |Disambiguate nullary type constructors and type variables.
fixInterface :: Interface -> Interface
fixInterface (Interface m is ds) = Interface m is $
  fix (Set.fromList (typeConstructors ds)) ds

class FixInterface a where
  fix :: Set.Set Ident -> a -> a

instance FixInterface a => FixInterface (Maybe a) where
  fix tcs = fmap (fix tcs)

instance FixInterface a => FixInterface [a] where
  fix tcs = map (fix tcs)

instance FixInterface IDecl where
  fix tcs (IDataDecl p tc k vs cs hs) =
    IDataDecl p tc k vs (fix tcs cs) hs
  fix tcs (INewtypeDecl p tc k vs nc hs) =
    INewtypeDecl p tc k vs (fix tcs nc) hs
  fix tcs (ITypeDecl p tc k vs ty) =
    ITypeDecl p tc k vs (fix tcs ty)
  fix tcs (IFunctionDecl p f cm n qty) =
    IFunctionDecl p f cm n (fix tcs qty)
  fix tcs (HidingClassDecl p cx cls k tvs fds) =
    HidingClassDecl p (fix tcs cx) cls k tvs fds
  fix tcs (IClassDecl p cx cls k tvs fds ms hs) =
    IClassDecl p (fix tcs cx) cls k tvs fds (fix tcs ms) hs
  fix tcs (IInstanceDecl p cx cls inst is m) =
    IInstanceDecl p (fix tcs cx) cls (fix tcs inst) is m
  fix _ d = d

instance FixInterface ConstrDecl where
  fix tcs (ConstrDecl p      c tys) = ConstrDecl p c (fix tcs tys)
  fix tcs (ConOpDecl  p ty1 op ty2) = ConOpDecl  p   (fix tcs ty1)
                                                op   (fix tcs ty2)
  fix tcs (RecordDecl p c fs)       = RecordDecl p c (fix tcs fs)

instance FixInterface FieldDecl where
  fix tcs (FieldDecl p ls ty) = FieldDecl p ls (fix tcs ty)

instance FixInterface NewConstrDecl where
  fix tcs (NewConstrDecl p c ty    ) = NewConstrDecl p c (fix tcs ty)
  fix tcs (NewRecordDecl p c (i,ty)) = NewRecordDecl p c (i, fix tcs ty)

instance FixInterface IMethodDecl where
  fix tcs (IMethodDecl p f a qty) = IMethodDecl p f a (fix tcs qty)

instance FixInterface QualTypeExpr where
  fix tcs (QualTypeExpr spi cx ty) = QualTypeExpr spi (fix tcs cx) (fix tcs ty)

instance FixInterface Constraint where
  fix tcs (Constraint spi qcls ty) = Constraint spi qcls (fix tcs ty)

instance FixInterface TypeExpr where
  fix tcs (ConstructorType spi tc)
    | not (isQualified tc) && not (isPrimTypeId tc) && tc' `Set.notMember` tcs
    = VariableType spi tc'
    | otherwise = ConstructorType spi tc
    where tc' = unqualify tc
  fix tcs (ApplyType  spi ty1 ty2) = ApplyType spi (fix tcs ty1) (fix tcs ty2)
  fix tcs (VariableType    spi tv)
    | tv `Set.member` tcs = ConstructorType spi (qualify tv)
    | otherwise           = VariableType spi tv
  fix tcs (TupleType      spi tys) = TupleType spi (fix tcs tys)
  fix tcs (ListType        spi ty) = ListType  spi (fix tcs ty)
  fix tcs (ArrowType  spi ty1 ty2) = ArrowType spi (fix tcs ty1) (fix tcs ty2)
  fix tcs (ParenType       spi ty) = ParenType spi (fix tcs ty)
  fix tcs (ForallType   spi vs ty) = ForallType spi vs (fix tcs ty)

typeConstructors :: [IDecl] -> [Ident]
typeConstructors ds = [tc | (QualIdent _ Nothing tc) <- foldr tyCons [] ds]
  where tyCons (IInfixDecl          _ _ _ _  ) tcs = tcs
        tyCons (HidingDataDecl     _ tc _ _  ) tcs = tc : tcs
        tyCons (IDataDecl      _ tc _ _ _ _  ) tcs = tc : tcs
        tyCons (INewtypeDecl   _ tc _ _ _ _  ) tcs = tc : tcs
        tyCons (ITypeDecl        _ tc _ _ _  ) tcs = tc : tcs
        tyCons (IFunctionDecl     _ _ _ _ _  ) tcs = tcs
        tyCons (HidingClassDecl   _ _ _ _ _ _) tcs = tcs
        tyCons (IClassDecl    _ _ _ _ _ _ _ _) tcs = tcs
        tyCons (IInstanceDecl   _ _ _ _ _ _  ) tcs = tcs
