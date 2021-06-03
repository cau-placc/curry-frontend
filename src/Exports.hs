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
import Base.CurryTypes (fromQualType, fromQualPredSet, fromQualPredType)
import Base.Messages
import Base.Types

import Env.Class
import Env.OpPrec          (OpPrecEnv, PrecInfo (..), OpPrec (..), qualLookupP)
import Env.Instance
import Env.TypeConstructor ( TCEnv, TypeInfo (..), tcKind, clsKinds
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
exportInterface' m es pEnv tcEnv vEnv clsEnv inEnv = Interface m imports decls'
  where
  tvs     = filter (`notElem` tcs) identSupply
  tcs     = mapMaybe (localIdent m) $ definedTypes decls'
  imports = map (IImportDecl NoPos) $ usedModules decls'
  precs   = foldr (infixDecl m pEnv) [] es
  types   = foldr (typeDecl m tcEnv clsEnv tvs) [] es
  values  = foldr (valueDecl m tcEnv vEnv tvs) [] es
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
  [PrecInfo _ (OpPrec f p)] -> IInfixDecl NoPos f p (qualUnqualify m op) : ds
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
    [AliasType tc' k n ty] -> ITypeDecl NoPos tc'' k' tvs' ty' : ds
      where tc'' = qualUnqualify m tc'
            k'   = fromKind' k n
            tvs' = take n tvs
            ty'  = fromQualType m tvs' ty
    [TypeClass qcls ks ms] -> IClassDecl NoPos cx qcls' kclsvars ms' hs : ds
      where qcls'    = qualUnqualify m qcls
            cx       = [ Constraint NoSpanInfo (qualUnqualify m qscls)
                           (map (VariableType NoSpanInfo) sclsvars)
                       | sclsInfo <- superClasses qcls clsEnv
                       , let (qscls, sclsvars) = applySuperClass tvs sclsInfo ]
            ks'      = map (flip fromKind' 0) ks
            kclsvars = zip tvs ks'
            ms'      = map (methodDecl m tvs) ms
            hs       = filter (`notElem` xs) (map methodName ms)
    _ -> internalError "Exports.typeDecl"
typeDecl _ _ _ _ _ _ = internalError "Exports.typeDecl: no pattern match"

iTypeDecl
  :: (Position -> QualIdent -> Maybe KindExpr -> [Ident] -> a -> [Ident] -> IDecl)
  -> ModuleIdent -> [Ident] -> QualIdent -> Kind -> a -> [Ident] -> IDecl
iTypeDecl f m tvs tc k x hs = f NoPos (qualUnqualify m tc) k' (take n tvs) x hs
  where n  = kindArity k
        k' = fromKind' k n

constrDecl :: ModuleIdent -> Int -> [Ident] -> DataConstr -> ConstrDecl
constrDecl m _ tvs (DataConstr c [ty1, ty2])
  | isInfixOp c = ConOpDecl NoSpanInfo ty1' c ty2'
  where [ty1', ty2'] = map (fromQualType m tvs) [ty1, ty2]
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

-- When exporting a class method, we have to remove the implicit class
-- constraint. Due to the sorting of the predicate set, this is fortunately very
-- easy. The implicit class constraint is marked with an 'ICC' flag, which
-- causes it to always be the minimum element of the predicate set.

methodDecl :: ModuleIdent -> [Ident] -> ClassMethod -> IMethodDecl
methodDecl m tvs (ClassMethod f a (PredType ps ty)) = IMethodDecl NoPos f a $
  fromQualPredType m tvs $ PredType (Set.deleteMin ps) ty

valueDecl
  :: ModuleIdent -> TCEnv -> ValueEnv -> [Ident] -> Export -> [IDecl] -> [IDecl]
valueDecl m tcEnv vEnv tvs (Export     _ f) ds = case qualLookupValue f vEnv of
  [Value _ cm a (ForAll _ pty)] ->
    IFunctionDecl NoPos (qualUnqualify m f)
      (fmap (flip take tvs . length . flip (clsKinds m) tcEnv) cm) a
      (fromQualPredType m tvs pty) : ds
  [Label _ _ _ ] -> ds -- Record labels are collected somewhere else.
  _ -> internalError $ "Exports.valueDecl: " ++ show f
valueDecl _ _ _ _ (ExportTypeWith _ _ _) ds = ds
valueDecl _ _ _ _ _ _ = internalError "Exports.valueDecl: no pattern match"

-- Transforms an entry of the instance environment into an interface instance
-- declaration and adds it to a list of instance declarations, if neither the
-- class nor any of the type constructors of the instance entry are declared in
-- same module as the instance (orphan instance). Otherwise, the given instance
-- declaration list is returned unaltered.
instDecl :: ModuleIdent -> TCEnv -> [Ident] -> InstIdent -> InstInfo -> [IDecl]
         -> [IDecl]
instDecl m tcEnv tvs ident@(cls, tcs) info@(m', _, _) ds
  | qidModule cls /= Just m' && all ((/= Just m') . qidModule) tcs =
    iInstDecl m tcEnv tvs ident info : ds
  | otherwise = ds

-- Transforms an entry of the instance environment into an interface instance
-- declaration.
iInstDecl :: ModuleIdent -> TCEnv -> [Ident] -> InstIdent -> InstInfo -> IDecl
iInstDecl m tcEnv tvs (cls, tcs) (m', ps, is) =
  IInstanceDecl NoPos cx (qualUnqualify m cls) tys is mm
 where
  cx  = fromQualPredSet m tvs ps
  tys = map (fromQualType m tvs) (tcsToTypes 0 tcs (clsKinds m cls tcEnv))
  mm  = if m == m' then Nothing else Just m'
  
  -- TODO: The following assumes that every type variable can only occur once in
  --         an instance head. This should be changed with FlexibleInstances.
  tcsToTypes :: Int -> [QualIdent] -> [Kind] -> [Type]
  tcsToTypes minVar (tc : tcs') (k : ks) =
    let n    = kindArity (tcKind m tc tcEnv) - kindArity k
        ntvs = map TypeVariable [minVar .. minVar + n - 1]
    in applyType (TypeConstructor tc) ntvs : tcsToTypes (minVar + n) tcs' ks
  tcsToTypes _ [] [] = []
  tcsToTypes _ _  _  = internalError $ "Exports.iInstDecl: Different number " ++
     "of class kinds and instance types for " ++ show (cls, tcs)

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
  modules (IInfixDecl             _ _ _ op) = modules op
  modules (HidingDataDecl         _ tc _ _) = modules tc
  modules (IDataDecl         _ tc _ _ cs _) = modules tc . modules cs
  modules (INewtypeDecl      _ tc _ _ nc _) = modules tc . modules nc
  modules (ITypeDecl           _ tc _ _ ty) = modules tc . modules ty
  modules (IFunctionDecl       _ f _ _ qty) = modules f . modules qty
  modules (HidingClassDecl      _ cx cls _) = modules cx . modules cls
  modules (IClassDecl      _ cx cls _ ms _) =
    modules cx . modules cls . modules ms
  modules (IInstanceDecl _ cx cls tys _ mm) =
    modules cx . modules cls . modules tys . modules mm

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
  modules (Constraint _ cls tys) = modules cls . modules tys

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
-- interface for all those types and classes which were used in the interface
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
iInfo (IInfixDecl            _ _ _ _) = IOther
iInfo (HidingDataDecl       _ tc _ _) = IType tc
iInfo (IDataDecl        _ tc _ _ _ _) = IType tc
iInfo (INewtypeDecl     _ tc _ _ _ _) = IType tc
iInfo (ITypeDecl           _ _ _ _ _) = IOther
iInfo (HidingClassDecl     _ _ cls _) = IClass cls
iInfo (IClassDecl      _ _ cls _ _ _) = IClass cls
iInfo (IInstanceDecl _ _ cls tys _ _) = IInst (cls, map typeConstr tys)
iInfo (IFunctionDecl       _ _ _ _ _) = IOther

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
 where
  hiddenTypeDecl tc = case qualLookupTypeInfo (qualQualify m tc) tcEnv of
    [DataType     _ k  _] -> hidingDataDecl k
    [RenamingType _ k  _] -> hidingDataDecl k
    [TypeClass  cls ks _] -> hidingClassDecl ks $ superClasses cls clsEnv
    _                     ->
      internalError $ "Exports.hiddenTypeDecl: " ++ show tc
   where
    hidingDataDecl k = let n  = kindArity k
                           k' = fromKind' k n
                       in  HidingDataDecl NoPos tc k' $ take n tvs
    hidingClassDecl ks sclss =
      let cx       = [ Constraint NoSpanInfo (qualUnqualify m qscls)
                         (map (VariableType NoSpanInfo) sclsvars)
                     | sclsInfo <- sclss
                     , let (qscls, sclsvars) = applySuperClass tvs sclsInfo ]
          ks'      = map (flip fromKind' 0) ks
          kclsvars = zip tvs ks'
      in  HidingClassDecl NoPos cx tc kclsvars

-- Returns a list of the interface declarations of all instances in the instance
-- environment that share an instance type or the class with the given interface
-- info for a type or a class and could be used in other modules.
instances :: ModuleIdent -> TCEnv -> InstEnv -> [Ident] -> Set.Set IInfo
          -> IInfo -> [IDecl]
instances _ _ _ _ _ IOther = []
instances m tcEnv inEnv tvs is (IType tc) =
  [ iInstDecl m tcEnv tvs ident info
  | (ident@(cls, tcs), info@(m', _, _)) <- Map.toList inEnv
  -- Check if the given interface info type occurs in the instance
  , qualQualify m tc `elem` tcs
  -- Check if all types occuring in the instance could be used in other modules
  , all tcConditions tcs
  -- Check if the class of the instance could be used in other modules
  , if qidModule cls == Just m' then Set.member (IClass (qualUnqualify m cls)) is
  -- Check if the instance is not an orphan instance already added in 'instDecl'
  -- TODO: It seems unnecessary to filter these out.
                                else any ((== Just m') . qidModule) tcs ]
 where
  -- Checks if an instance type with the given name could be used in other
  -- modules. This is considered to be the case if the type (1) is the one
  -- originally requested, (2) is a primary type like a list, (3) has been
  -- defined in another module or (4) is already part of the exports.
  -- TODO: Why is (2) tested? It should be implied by (3).
  tcConditions :: QualIdent -> Bool
  tcConditions tc' = tc' == qualQualify m tc || isPrimTypeId tc' ||
    qidModule tc' /= Just m || Set.member (IType (qualUnqualify m tc')) is

instances m tcEnv inEnv tvs is (IClass cls) =
  [ iInstDecl m tcEnv tvs ident info
  | (ident@(cls', tcs), info@(m', _, _)) <- Map.toList inEnv
  -- Check if the given interface info class is the class of the instance
  , qualQualify m cls == cls'
  -- Check if the instance is defined in the same module as the class
  -- TODO: Why is this checked?
  , qidModule cls' == Just m'
  -- Check if all types occuring in the instance could be used in other modules
  -- TODO: Why is m /= m' checked? In this case, the second of the tcConditions
  --         should apply as well for every type.
  , m /= m' || all tcConditions tcs ]
 where
  -- Checks if an instance type with the given name could be used in other
  -- modules. This is considered to be the case if the type (1) is a primary
  -- type like a list, (2) has been defined in another module or (3) is already
  -- part of the exports.
  tcConditions :: QualIdent -> Bool
  tcConditions tc = isPrimTypeId tc || qidModule tc /= Just m ||
    Set.member (IType (qualUnqualify m tc)) is
instances _ _ _ _ _ (IInst _) = []

definedTypes :: [IDecl] -> [QualIdent]
definedTypes ds = foldr definedType [] ds
  where
  definedType :: IDecl -> [QualIdent] -> [QualIdent]
  definedType (HidingDataDecl   _ tc _ _) tcs = tc : tcs
  definedType (IDataDecl    _ tc _ _ _ _) tcs = tc : tcs
  definedType (INewtypeDecl _ tc _ _ _ _) tcs = tc : tcs
  definedType (ITypeDecl      _ tc _ _ _) tcs = tc : tcs
  definedType (HidingClassDecl _ _ cls _) tcs = cls : tcs
  definedType (IClassDecl  _ _ cls _ _ _) tcs = cls : tcs
  definedType _                           tcs = tcs

class HasType a where
  usedTypes :: a -> [QualIdent] -> [QualIdent]

instance HasType a => HasType (Maybe a) where
  usedTypes = maybe id usedTypes

instance HasType a => HasType [a] where
  usedTypes xs tcs = foldr usedTypes tcs xs

instance HasType IDecl where
  usedTypes (IInfixDecl             _ _ _ _) = id
  usedTypes (HidingDataDecl         _ _ _ _) = id
  usedTypes (IDataDecl         _ _ _ _ cs _) = usedTypes cs
  usedTypes (INewtypeDecl      _ _ _ _ nc _) = usedTypes nc
  usedTypes (ITypeDecl           _ _ _ _ ty) = usedTypes ty
  usedTypes (IFunctionDecl      _ _ _ _ qty) = usedTypes qty
  usedTypes (HidingClassDecl       _ cx _ _) = usedTypes cx
  usedTypes (IClassDecl       _ cx _ _ ms _) = usedTypes cx . usedTypes ms
  usedTypes (IInstanceDecl _ cx cls tys _ _) =
    usedTypes cx . (cls :) . usedTypes tys

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
  usedTypes (Constraint _ cls tys) = (cls :) . usedTypes tys

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
