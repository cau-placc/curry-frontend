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
import qualified Data.Map   as Map ( Map, delete, fromListWith, lookup
                                   , mapKeysWith, toList)
import           Data.Maybe        (mapMaybe)
import qualified Data.Set   as Set ( Set, delete, empty, insert, deleteMin
                                   , fromList, member, toList )

import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Ident
import Curry.Syntax

import Base.CurryKinds (fromKind', fromClassKind)
import Base.CurryTypes (fromQualType, fromQualPredType, fromQualPredTypes)
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
exportInterface' m es pEnv tcEnv vEnv clsEnv inEnv = Interface m imports decls'
  where
  tvs     = filter (`notElem` tcs) identSupply
  tcs     = mapMaybe (localIdent m) $ definedTypes decls'
  imports = map (IImportDecl NoPos) $ usedModules decls'
  precs   = foldr (infixDecl m pEnv) [] es
  types   = foldr (typeDecl m tcEnv clsEnv tvs) [] es
  values  = foldr (valueDecl m tcEnv vEnv tvs) [] es
  (inExps, insts) = getExportedInsts m tcEnv inEnv tvs (initInstExports m inEnv)
  decls   = precs ++ types ++ values ++ insts
  decls'  = closeInterface m tcEnv clsEnv inEnv tvs Set.empty inExps decls

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
    [TypeClass qcls k ms] -> IClassDecl NoPos cx qcls' k' clsvars ms' hs : ds
      where qcls'   = qualUnqualify m qcls
            cx      = [ Constraint NoSpanInfo (qualUnqualify m qscls)
                          (map (VariableType NoSpanInfo) sclsvars)
                      | sclsInfo <- superClasses qcls clsEnv
                      , let (qscls, sclsvars) = applySuperClass tvs sclsInfo ]
            n       = kindArity k
            k'      = fromClassKind k n
            clsvars = take n tvs
            ms'     = map (methodDecl m tvs) ms
            hs      = filter (`notElem` xs) (map methodName ms)
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
      (fmap (flip take tvs . kindArity . flip (clsKind m) tcEnv) cm) a
      (fromQualPredType m tvs pty) : ds
  [Label _ _ _ ] -> ds -- Record labels are collected somewhere else.
  _ -> internalError $ "Exports.valueDecl: " ++ show f
valueDecl _ _ _ _ (ExportTypeWith _ _ _) ds = ds
valueDecl _ _ _ _ _ _ = internalError "Exports.valueDecl: no pattern match"

-- The instance export map maps sets of class and type names to the instance
-- idents that have to be exported, if all entries of the set are exported.
type InstExportMap = Map.Map (Set.Set QualIdent) [InstIdent]

-- 'initInstExports' initializes the instance export map by going through the
-- instance environment and entering all instance idents under the set of class
-- and type names that have to be exported for the instance to be exported.
--
-- For instances defined in the current module, these are the names of all
-- classes and types occurring in the instance head that are from the current
-- module as well. An instance can only be used if its class and all of its
-- instance types are in scope, so if any of these is not exported, the
-- instance cannot be used outside of the current module.
--
-- For instances defined in imported modules however, we cannot use the same
-- approach and require all classes and types of the instance that are defined
-- in the same module as the instance to be exported by the current module.
-- For example, if a module M defined a class C, a type T and an instance C T;
-- a module N imported M in its entirety, but only exported C; and a module O
-- also imported M in its entirety, but only exported T, then a module P
-- importing N and O would have both C and T in scope, but not the instance C T,
-- if this approach was used. But if we instead decide on a single one of the
-- classes and types defined in the same module as the instance and always
-- export the instance, if this class or type is exported, then this problem is
-- solved while limiting the number of unnecessary instance exports and imports.
--
-- Instances where neither the instance's class nor any of its instance types
-- are defined in the same module as the instance (called orphan instances) are
-- always exported if they are in the instance environment. This has to be done
-- as we cannot limit the modules that could use these instances like we can
-- with other instances.
initInstExports :: ModuleIdent -> InstEnv -> InstExportMap
initInstExports m = Map.fromListWith (++) . map instExpMapEntry . Map.toList
 where
  instExpMapEntry :: (InstIdent, InstInfo) -> (Set.Set QualIdent, [InstIdent])
  instExpMapEntry (instId@(cls, tcs), (m', _, _)) =
    let select = if m == m' then id else take 1
    in ( Set.fromList $ select $ filter ((== Just m') . qidModule) $ cls : tcs
       , [instId] )

-- Removes the instances that currently have to be exported from the instance
-- export map, converts them to interface declarations and returns the updated
-- instance export map together with the interface declarations.
getExportedInsts :: ModuleIdent -> TCEnv -> InstEnv -> [Ident] -> InstExportMap
                 -> (InstExportMap, [IDecl])
getExportedInsts m tcEnv inEnv tvs inExps =
  ( Map.delete Set.empty inExps
  , maybe [] (map (iInstDecl m tcEnv inEnv tvs)) (Map.lookup Set.empty inExps)
  )

-- Transforms an entry of the instance environment into an interface instance
-- declaration.
iInstDecl :: ModuleIdent -> TCEnv -> InstEnv -> [Ident] -> InstIdent -> IDecl
iInstDecl m tcEnv inEnv tvs instId@(cls, tcs) =
  IInstanceDecl NoPos cx (qualUnqualify m cls) tys is mm
 where
  (m', ps, is) = case lookupInstInfo instId inEnv of
                   Just instInfo -> instInfo
                   Nothing -> internalError $ "Exports.iInstDecl: Couldn't " ++
                                "find instance information for " ++ show instId
  (cx, tys) = fromQualPredTypes m tvs $
    PredTypes ps (tcsToTypes 0 tcs (clsKind m cls tcEnv))
  mm  = if m == m' then Nothing else Just m'
  
  -- TODO: The following assumes that every type variable can only occur once in
  --         an instance head. This should be changed with FlexibleInstances.
  tcsToTypes :: Int -> [QualIdent] -> Kind -> [Type]
  tcsToTypes minVar (tc : tcs') (KindArrow k1 k2) =
    let n    = kindArity (tcKind m tc tcEnv) - kindArity k1
        ntvs = map TypeVariable [minVar .. minVar + n - 1]
    in applyType (TypeConstructor tc) ntvs : tcsToTypes (minVar + n) tcs' k2
  tcsToTypes _ [] KindConstraint = []
  tcsToTypes _ _ _ = internalError $ "Exports.iInstDecl: " ++
    "Kind arity does not match number of instance types for " ++ show (cls, tcs)

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
  modules (HidingClassDecl    _ cx cls _ _) = modules cx . modules cls
  modules (IClassDecl    _ cx cls _ _ ms _) =
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
iInfo (HidingClassDecl   _ _ cls _ _) = IClass cls
iInfo (IClassDecl    _ _ cls _ _ _ _) = IClass cls
iInfo (IInstanceDecl _ _ cls tys _ _) = IInst (cls, map typeConstr tys)
iInfo (IFunctionDecl       _ _ _ _ _) = IOther

closeInterface :: ModuleIdent -> TCEnv -> ClassEnv -> InstEnv -> [Ident]
               -> Set.Set IInfo -> InstExportMap -> [IDecl] -> [IDecl]
closeInterface _ _ _ _ _ _ _ [] = []
closeInterface m tcEnv clsEnv inEnv tvs is inExps (d:ds)
  | i == IOther       =
    d : closeInterface m tcEnv clsEnv inEnv tvs is inExps ds'
  | i `Set.member` is = closeInterface m tcEnv clsEnv inEnv tvs is inExps ds
  | otherwise         =
    d : closeInterface m tcEnv clsEnv inEnv tvs (Set.insert i is) inExps' ds'
  where i = iInfo d
        (inExps', ds') = (ds ++) <$> ((hiddenTypes m tcEnv clsEnv tvs d ++) <$>
           getExportedInsts m tcEnv inEnv tvs (updateInstExports m i inExps))

hiddenTypes :: ModuleIdent -> TCEnv -> ClassEnv -> [Ident] -> IDecl -> [IDecl]
hiddenTypes m tcEnv clsEnv tvs d =
  map hiddenTypeDecl $ filter (not . isPrimTypeId) (usedTypes d [])
 where
  hiddenTypeDecl tc = case qualLookupTypeInfo (qualQualify m tc) tcEnv of
    [DataType     _ k _] -> hidingDataDecl k
    [RenamingType _ k _] -> hidingDataDecl k
    [TypeClass  cls k _] -> hidingClassDecl k $ superClasses cls clsEnv
    _                    ->
      internalError $ "Exports.hiddenTypeDecl: " ++ show tc
   where
    hidingDataDecl k = let n  = kindArity k
                           k' = fromKind' k n
                       in  HidingDataDecl NoPos tc k' $ take n tvs
    hidingClassDecl k sclss =
      let cx       = [ Constraint NoSpanInfo (qualUnqualify m qscls)
                         (map (VariableType NoSpanInfo) sclsvars)
                     | sclsInfo <- sclss
                     , let (qscls, sclsvars) = applySuperClass tvs sclsInfo ]
          n       = kindArity k
          k'      = fromClassKind k n
          clsvars = take n tvs
      in  HidingClassDecl NoPos cx tc k' clsvars

-- Updates the instance export map by removing the given interface entry from
-- the sets of class and type names that have to be exported before the
-- associated instances are exported.
updateInstExports :: ModuleIdent -> IInfo -> InstExportMap -> InstExportMap
updateInstExports m (IType  tc)  =
  Map.mapKeysWith (++) (Set.delete (qualQualify m tc))
updateInstExports m (IClass cls) =
  Map.mapKeysWith (++) (Set.delete (qualQualify m cls))
updateInstExports _ _            = id

definedTypes :: [IDecl] -> [QualIdent]
definedTypes ds = foldr definedType [] ds
  where
  definedType :: IDecl -> [QualIdent] -> [QualIdent]
  definedType (HidingDataDecl     _ tc _ _) tcs = tc : tcs
  definedType (IDataDecl      _ tc _ _ _ _) tcs = tc : tcs
  definedType (INewtypeDecl   _ tc _ _ _ _) tcs = tc : tcs
  definedType (ITypeDecl        _ tc _ _ _) tcs = tc : tcs
  definedType (HidingClassDecl _ _ cls _ _) tcs = cls : tcs
  definedType (IClassDecl  _ _ cls _ _ _ _) tcs = cls : tcs
  definedType _                             tcs = tcs

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
  usedTypes (HidingClassDecl     _ cx _ _ _) = usedTypes cx
  usedTypes (IClassDecl     _ cx _ _ _ ms _) = usedTypes cx . usedTypes ms
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
