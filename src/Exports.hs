{- |
    Module      :  $Header$
    Description :  Computation of export interface
    Copyright   :  (c) 2000 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2016 Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the computation of the exported interface of a
    compiled module. The function 'exportInterface' uses the expanded export
    specifications and the corresponding environments in order to compute
    the interface of the module.
-}
module Exports (exportInterface) where

import           Data.List         (nub)
import qualified Data.Map   as Map (foldrWithKey, toList)
import           Data.Maybe        (mapMaybe)
import qualified Data.Set   as Set ( Set, empty, insert, deleteMin, fromList
                                   , member, toList )

import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Ident
import Curry.Syntax

import Base.CurryKinds (fromKind')
import Base.CurryTypes (fromQualType, fromQualPredType)
import Base.Messages
import Base.Types

import Env.Class
import Env.OpPrec          (OpPrecEnv, PrecInfo (..), OpPrec (..), qualLookupP)
import Env.Instance
import Env.TypeConstructor ( TCEnv, TypeInfo (..), tcKind, clsKind
                           , qualLookupTypeInfo )
import Env.Value           (ValueEnv, ValueInfo (..), qualLookupValue)

import CompilerEnv

import Base.Kinds

-- ---------------------------------------------------------------------------
-- Computation of the interface
-- ---------------------------------------------------------------------------

-- After checking that the interface is not ambiguous, the compiler
-- generates the interface's declarations from the list of exported
-- functions and values. In order to make the interface more stable
-- against private changes in the module, we remove the hidden data
-- constructors of a data type in the interface when they occur
-- right-most in the declaration. In addition, newtypes whose constructor
-- is not exported are transformed into (abstract) data types.
--
-- If a type is imported from another module, its name is qualified with
-- the name of the module where it is defined. The same applies to an
-- exported function.

exportInterface :: CompilerEnv -> Module a -> Interface
exportInterface env (Module _ _ _ m (Just (Exporting _ es)) _ _) =
  exportInterface' m es (opPrecEnv env) (tyConsEnv env) (valueEnv env)
    (classEnv env) (instEnv env)
exportInterface _   (Module _ _ _ _ Nothing                 _ _) =
  internalError "Exports.exportInterface: no export specification"

exportInterface' :: ModuleIdent -> [Export] -> OpPrecEnv -> TCEnv -> ValueEnv
                 -> ClassEnv -> InstEnv -> Interface
exportInterface' m es pEnv tcEnv vEnv clsEnv inEnv = Interface m imports decls' (Just (mkOriginPragma m))
  where
  tvs     = filter (`notElem` tcs) identSupply
  tcs     = mapMaybe (localIdent m) $ definedTypes decls'
  imports = (\m' -> IImportDecl NoPos m' (Just (mkOriginPragma m'))) <$> usedModules decls'
  precs   = foldr (infixDecl m pEnv) [] es
  types   = foldr (typeDecl m tcEnv clsEnv tvs) [] es
  values  = foldr (valueDecl m vEnv tvs) [] es
  insts   = Map.foldrWithKey (instDecl m tcEnv tvs) [] inEnv
  decls   = precs ++ types ++ values ++ insts
  decls'  = closeInterface m tcEnv clsEnv inEnv tvs Set.empty decls

infixDecl :: ModuleIdent -> OpPrecEnv -> Export -> [IDecl] -> [IDecl]
infixDecl m pEnv (Export             _ f) ds = iInfixDecl m pEnv f ds
infixDecl m pEnv (ExportTypeWith _ tc cs) ds =
  foldr (iInfixDecl m pEnv . qualifyLike tc) ds cs
infixDecl _ _ _ _ = internalError "Exports.infixDecl: no pattern match"

iInfixDecl :: ModuleIdent -> OpPrecEnv -> QualIdent -> [IDecl] -> [IDecl]
iInfixDecl m pEnv op ds = case qualLookupP op pEnv of
  []                        -> ds
  [PrecInfo _ (OpPrec f p)] -> IInfixDecl (Just (mkOriginPragma op)) NoPos f p (qualUnqualify m op) : ds
  _                         -> internalError "Exports.infixDecl"

-- Data types and renaming types whose constructors and field labels are
-- not exported are exported as abstract types, i.e., their constructors
-- do not appear in the interface. If only some constructors or field
-- labels of a type are not exported all constructors appear in the
-- interface, but a pragma marks the constructors and field labels which
-- are not exported as hidden to prevent their use in user code.

typeDecl :: ModuleIdent -> TCEnv -> ClassEnv -> [Ident] -> Export -> [IDecl]
         -> [IDecl]
typeDecl _ _     _      _   (Export             _ _) ds = ds
typeDecl m tcEnv clsEnv tvs (ExportTypeWith _ tc xs) ds =
  case qualLookupTypeInfo tc tcEnv of
    [DataType tc' k cs]
      | null xs   -> iTypeDecl IDataDecl m tvs tc' k []  [] : ds
      | otherwise -> iTypeDecl IDataDecl m tvs tc' k cs' hs : ds
      where hs    = filter (`notElem` xs) (csIds ++ ls)
            cs'   = map (constrDecl m n tvs) cs
            ls    = nub (concatMap recordLabels cs')
            csIds = map constrIdent cs
            n = kindArity k
    [RenamingType tc' k c]
      | null xs   -> iTypeDecl IDataDecl    m tvs tc' k [] [] : ds
      | otherwise -> iTypeDecl INewtypeDecl m tvs tc' k nc hs : ds
      where hs  = filter (`notElem` xs) (cId : ls)
            nc  = newConstrDecl m tvs c
            ls  = nrecordLabels nc
            cId = constrIdent c
    [AliasType tc' k n ty] -> ITypeDecl (Just (mkOriginPragma tc')) NoPos tc'' k' tvs' ty' : ds
      where tc'' = qualUnqualify m tc'
            k'   = fromKind' k n
            tvs' = take n tvs
            ty'  = fromQualType m tvs' ty
    [TypeClass qcls k ms] -> IClassDecl (Just (mkOriginPragma qcls)) NoPos cx qcls' k' tv ms' hs : ds
      where qcls' = qualUnqualify m qcls
            cx    = [ Constraint NoSpanInfo (qualUnqualify m scls)
                        (VariableType NoSpanInfo tv)
                    | scls <- superClasses qcls clsEnv ]
            k'    = fromKind' k 0
            tv    = head tvs
            ms'   = map (methodDecl m tvs) ms
            hs    = filter (`notElem` xs) (map methodName ms)
    _ -> internalError "Exports.typeDecl"
typeDecl _ _ _ _ _ _ = internalError "Exports.typeDecl: no pattern match"

iTypeDecl
  :: (Maybe OriginPragma -> Position -> QualIdent -> Maybe KindExpr -> [Ident] -> a -> [Ident] -> IDecl)
  -> ModuleIdent -> [Ident] -> QualIdent -> Kind -> a -> [Ident] -> IDecl
iTypeDecl f m tvs tc k x hs = f (Just (mkOriginPragma tc)) NoPos (qualUnqualify m tc) k' (take n tvs) x hs
  where n  = kindArity k
        k' = fromKind' k n

constrDecl :: ModuleIdent -> Int -> [Ident] -> DataConstr -> ConstrDecl
constrDecl m _ tvs (DataConstr c [ty1, ty2])
  | isInfixOp c = ConOpDecl NoSpanInfo ty1' c ty2'
  where ty1' = fromQualType m tvs ty1
        ty2' = fromQualType m tvs ty2
constrDecl m _ tvs (DataConstr c tys) =
  ConstrDecl NoSpanInfo c tys'
  where tys' = map (fromQualType m tvs) tys
constrDecl m _ tvs (RecordConstr c ls tys) =
  RecordDecl NoSpanInfo c fs
  where
    tys' = map (fromQualType m tvs) tys
    fs   = zipWith (FieldDecl NoSpanInfo . return) ls tys'

newConstrDecl :: ModuleIdent -> [Ident] -> DataConstr -> NewConstrDecl
newConstrDecl m tvs (DataConstr c tys)
  = NewConstrDecl NoSpanInfo c (fromQualType m tvs (head tys))
newConstrDecl m tvs (RecordConstr c ls tys)
  = NewRecordDecl NoSpanInfo c (head ls, fromQualType m tvs (head tys))

-- When exporting a class method, we have to remove the implicit class context.
-- Due to the sorting of the predicate set, this is fortunatly very easy. The
-- implicit class context is always the minimum element as the class variable
-- is assigned the index 0 and no other constraints on it are allowed.

methodDecl :: ModuleIdent -> [Ident] -> ClassMethod -> IMethodDecl
methodDecl m tvs (ClassMethod f a (PredType ps ty)) = IMethodDecl NoPos f a $
  fromQualPredType m tvs $ PredType (Set.deleteMin ps) ty

valueDecl :: ModuleIdent -> ValueEnv -> [Ident] -> Export -> [IDecl] -> [IDecl]
valueDecl m vEnv tvs (Export     _ f) ds = case qualLookupValue f vEnv of
  [Value _ cm a (ForAll _ pty)] ->
    IFunctionDecl (Just (mkOriginPragma f)) NoPos (qualUnqualify m f)
      (fmap (const (head tvs)) cm) a (fromQualPredType m tvs pty) : ds
  [Label _ _ _ ] -> ds -- Record labels are collected somewhere else.
  _ -> internalError $ "Exports.valueDecl: " ++ show f
valueDecl _ _ _ (ExportTypeWith _ _ _) ds = ds
valueDecl _ _ _ _ _ = internalError "Exports.valueDecl: no pattern match"

instDecl :: ModuleIdent -> TCEnv -> [Ident] -> InstIdent -> InstInfo -> [IDecl]
         -> [IDecl]
instDecl m tcEnv tvs ident@(cls, tc) info@(m', _, _) ds
  | qidModule cls /= Just m' && qidModule tc /= Just m' =
    iInstDecl m tcEnv tvs ident info : ds
  | otherwise = ds

iInstDecl :: ModuleIdent -> TCEnv -> [Ident] -> InstIdent -> InstInfo -> IDecl
iInstDecl m tcEnv tvs (cls, tc) (m', ps, is) =
  IInstanceDecl (Just (mkOriginPragma cls)) NoPos cx (qualUnqualify m cls) ty is mm
  where pty = PredType ps $ applyType (TypeConstructor tc) $
                map TypeVariable [0 .. n-1]
        QualTypeExpr _ cx ty = fromQualPredType m tvs pty
        n = kindArity (tcKind m tc tcEnv) - kindArity (clsKind m cls tcEnv)
        mm = if m == m' then Nothing else Just m'

-- The compiler determines the list of imported modules from the set of
-- module qualifiers that are used in the interface. Careful readers
-- probably will have noticed that the functions above carefully strip
-- the module prefix from all entities that are defined in the current
-- module. Note that the list of modules returned from
-- 'usedModules' is not necessarily a subset of the modules that
-- were imported into the current module. This will happen when an
-- imported module re-exports entities from another module. E.g., given
-- the three modules
--
-- @
-- module A where { data A = A; }
-- module B(A(..)) where { import A; }
-- module C where { import B; x = A; }
-- @
--
-- the interface for module @C@ will import module @A@ but not module @B@.

usedModules :: [IDecl] -> [ModuleIdent]
usedModules ds = nub' (modules ds [])
  where nub' = Set.toList . Set.fromList

class HasModule a where
  modules :: a -> [ModuleIdent] -> [ModuleIdent]

instance HasModule a => HasModule (Maybe a) where
  modules = maybe id modules

instance HasModule a => HasModule [a] where
  modules xs ms = foldr modules ms xs

instance HasModule IDecl where
  modules (IInfixDecl            _ _ _ _ op) = modules op
  modules (HidingDataDecl        _ _ tc _ _) = modules tc
  modules (IDataDecl        _ _ tc _ _ cs _) = modules tc . modules cs
  modules (INewtypeDecl     _ _ tc _ _ nc _) = modules tc . modules nc
  modules (ITypeDecl          _ _ tc _ _ ty) = modules tc . modules ty
  modules (IFunctionDecl      _ _ f _ _ qty) = modules f . modules qty
  modules (HidingClassDecl   _ _ cx cls _ _) = modules cx . modules cls
  modules (IClassDecl   _ _ cx cls _ _ ms _) =
    modules cx . modules cls . modules ms
  modules (IInstanceDecl _ _ cx cls ty _ mm) =
    modules cx . modules cls . modules ty . modules mm

instance HasModule ConstrDecl where
  modules (ConstrDecl    _ _ tys) = modules tys
  modules (ConOpDecl _ ty1 _ ty2) = modules ty1 . modules ty2
  modules (RecordDecl     _ _ fs) = modules fs

instance HasModule FieldDecl where
  modules (FieldDecl _ _ ty) = modules ty

instance HasModule NewConstrDecl where
  modules (NewConstrDecl _ _      ty) = modules ty
  modules (NewRecordDecl _ _ (_, ty)) = modules ty

instance HasModule IMethodDecl where
  modules (IMethodDecl _ _ _ qty) = modules qty

instance HasModule Constraint where
  modules (Constraint _ cls ty) = modules cls . modules ty

instance HasModule TypeExpr where
  modules (ConstructorType _ tc) = modules tc
  modules (ApplyType  _ ty1 ty2) = modules ty1 . modules ty2
  modules (VariableType     _ _) = id
  modules (TupleType      _ tys) = modules tys
  modules (ListType        _ ty) = modules ty
  modules (ArrowType  _ ty1 ty2) = modules ty1 . modules ty2
  modules (ParenType       _ ty) = modules ty
  modules (ForallType    _ _ ty) = modules ty

instance HasModule QualTypeExpr where
  modules (QualTypeExpr _ cx ty) = modules cx . modules ty

instance HasModule QualIdent where
  modules = modules . qidModule

instance HasModule ModuleIdent where
  modules = (:)

-- After the interface declarations have been computed, the compiler
-- eventually must add hidden (data) type and class declarations to the
-- interface for all those types and classs which were used in the interface
-- but not exported from the current module, so that these type constructors
-- can always be distinguished from type variables. Besides hidden type and
-- class declarations, the compiler also adds instance declarations to the
-- interface. Since class and instance declarations added to an interface can
-- require the inclusion of further classes by their respective contexts,
-- closing an interface is implemented as a fix-point computation which
-- starts from the initial interface.

data IInfo = IOther | IType QualIdent | IClass QualIdent | IInst InstIdent
  deriving (Eq, Ord)

iInfo :: IDecl -> IInfo
iInfo (IInfixDecl           _ _ _ _ _) = IOther
iInfo (HidingDataDecl      _ _ tc _ _) = IType tc
iInfo (IDataDecl       _ _ tc _ _ _ _) = IType tc
iInfo (INewtypeDecl    _ _ tc _ _ _ _) = IType tc
iInfo (ITypeDecl          _ _ _ _ _ _) = IOther
iInfo (HidingClassDecl  _ _ _ cls _ _) = IClass cls
iInfo (IClassDecl   _ _ _ cls _ _ _ _) = IClass cls
iInfo (IInstanceDecl _ _ _ cls ty _ _) = IInst (cls, typeConstr ty)
iInfo (IFunctionDecl      _ _ _ _ _ _) = IOther

closeInterface :: ModuleIdent -> TCEnv -> ClassEnv -> InstEnv -> [Ident]
               -> Set.Set IInfo -> [IDecl] -> [IDecl]
closeInterface _ _ _ _ _ _ [] = []
closeInterface m tcEnv clsEnv inEnv tvs is (d:ds)
  | i == IOther       =
    d : closeInterface m tcEnv clsEnv inEnv tvs is (ds ++ ds')
  | i `Set.member` is = closeInterface m tcEnv clsEnv inEnv tvs is ds
  | otherwise         =
    d : closeInterface m tcEnv clsEnv inEnv tvs (Set.insert i is) (ds ++ ds')
  where i   = iInfo d
        ds' = hiddenTypes m tcEnv clsEnv tvs d ++
                instances m tcEnv inEnv tvs is i

hiddenTypes :: ModuleIdent -> TCEnv -> ClassEnv -> [Ident] -> IDecl -> [IDecl]
hiddenTypes m tcEnv clsEnv tvs d =
  map hiddenTypeDecl $ filter (not . isPrimTypeId) (usedTypes d [])
  where hiddenTypeDecl tc = case qualLookupTypeInfo (qualQualify m tc) tcEnv of
          [DataType       _ k _] -> hidingDataDecl k
          [RenamingType   _ k _] -> hidingDataDecl k
          [TypeClass    cls k _] -> hidingClassDecl k $ superClasses cls clsEnv
          _                      ->
            internalError $ "Exports.hiddenTypeDecl: " ++ show tc
          where hidingDataDecl k =
                  let n = kindArity k
                      k' = fromKind' k n
                  in  HidingDataDecl (Just (mkOriginPragma tc)) NoPos tc k' $ take n tvs
                hidingClassDecl k sclss =
                  let cx = [ Constraint NoSpanInfo (qualUnqualify m scls)
                               (VariableType NoSpanInfo tv)
                           | scls <- sclss ]
                      tv = head tvs
                      k' = fromKind' k 0
                  in  HidingClassDecl (Just (mkOriginPragma tc)) NoPos cx tc k' tv

instances :: ModuleIdent -> TCEnv -> InstEnv -> [Ident] -> Set.Set IInfo
          -> IInfo -> [IDecl]
instances _ _ _ _ _ IOther = []
instances m tcEnv inEnv tvs is (IType tc) =
  [ iInstDecl m tcEnv tvs ident info
  | (ident@(cls, tc'), info@(m', _, _)) <- Map.toList inEnv,
    qualQualify m tc == tc',
    if qidModule cls == Just m' then Set.member (IClass (qualUnqualify m cls)) is
                                else qidModule tc' == Just m' ]
instances m tcEnv inEnv tvs is (IClass cls) =
  [ iInstDecl m tcEnv tvs ident info
  | (ident@(cls', tc), info@(m', _, _)) <- Map.toList inEnv,
    qualQualify m cls == cls',
    qidModule cls' == Just m',
    m /= m' || isPrimTypeId tc
            || qidModule tc /= Just m
            || Set.member (IType (qualUnqualify m tc)) is ]
instances _ _ _ _ _ (IInst _) = []

definedTypes :: [IDecl] -> [QualIdent]
definedTypes ds = foldr definedType [] ds
  where
  definedType :: IDecl -> [QualIdent] -> [QualIdent]
  definedType (HidingDataDecl     _ _ tc _ _) tcs = tc : tcs
  definedType (IDataDecl      _ _ tc _ _ _ _) tcs = tc : tcs
  definedType (INewtypeDecl   _ _ tc _ _ _ _) tcs = tc : tcs
  definedType (ITypeDecl      _ _ tc _ _ _  ) tcs = tc : tcs
  definedType (HidingClassDecl _ _ _ cls _ _) tcs = cls : tcs
  definedType (IClassDecl  _ _ _ cls _ _ _ _) tcs = cls : tcs
  definedType _                               tcs = tcs

class HasType a where
  usedTypes :: a -> [QualIdent] -> [QualIdent]

instance HasType a => HasType (Maybe a) where
  usedTypes = maybe id usedTypes

instance HasType a => HasType [a] where
  usedTypes xs tcs = foldr usedTypes tcs xs

instance HasType IDecl where
  usedTypes (IInfixDecl            _ _ _ _ _) = id
  usedTypes (HidingDataDecl        _ _ _ _ _) = id
  usedTypes (IDataDecl        _ _ _ _ _ cs _) = usedTypes cs
  usedTypes (INewtypeDecl     _ _ _ _ _ nc _) = usedTypes nc
  usedTypes (ITypeDecl         _ _ _ _ _ ty) = usedTypes ty
  usedTypes (IFunctionDecl     _ _ _ _ _ qty) = usedTypes qty
  usedTypes (HidingClassDecl    _ _ cx _ _ _) = usedTypes cx
  usedTypes (IClassDecl    _ _ cx _ _ _ ms _) = usedTypes cx . usedTypes ms
  usedTypes (IInstanceDecl _ _ cx cls ty _ _) =
    usedTypes cx . (cls :) . usedTypes ty

instance HasType ConstrDecl where
  usedTypes (ConstrDecl    _ _ tys) = usedTypes tys
  usedTypes (ConOpDecl _ ty1 _ ty2) =
    usedTypes ty1 . usedTypes ty2
  usedTypes (RecordDecl     _ _ fs) = usedTypes fs

instance HasType FieldDecl where
  usedTypes (FieldDecl _ _ ty) = usedTypes ty

instance HasType NewConstrDecl where
  usedTypes (NewConstrDecl      _ _ ty) = usedTypes ty
  usedTypes (NewRecordDecl _ _ (_, ty)) = usedTypes ty

instance HasType IMethodDecl where
  usedTypes (IMethodDecl _ _ _ qty) = usedTypes qty

instance HasType Constraint where
  usedTypes (Constraint _ cls ty) = (cls :) . usedTypes ty

instance HasType TypeExpr where
  usedTypes (ConstructorType _ tc) = (tc :)
  usedTypes (ApplyType _ ty1 ty2) = usedTypes ty1 . usedTypes ty2
  usedTypes (VariableType     _ _) = id
  usedTypes (TupleType      _ tys) = usedTypes tys
  usedTypes (ListType        _ ty) = usedTypes ty
  usedTypes (ArrowType  _ ty1 ty2) = usedTypes ty1 . usedTypes ty2
  usedTypes (ParenType       _ ty) = usedTypes ty
  usedTypes (ForallType    _ _ ty) = usedTypes ty

instance HasType QualTypeExpr where
  usedTypes (QualTypeExpr _ cx ty) = usedTypes cx . usedTypes ty
