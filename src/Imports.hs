{- |
    Module      :  $Header$
    Description :  Importing interface declarations
    Copyright   :  (c) 2000 - 2003 Wolfgang Lux
                       2011        Björn Peemöller
                       2016        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the function 'importModules' to bring the imported
    entities into the module's scope, and the function 'qualifyEnv' to
    qualify the environment prior to computing the export interface.
-}
module Imports (importInterfaces, importModules, qualifyEnv) where

import           Data.List                  (nubBy, find)
import qualified Data.Map            as Map
import           Data.Maybe                 (catMaybes, fromMaybe, isJust)
import qualified Data.Set            as Set

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Base.Monad
import Curry.Syntax

import Base.CurryKinds (toKind')
import Base.CurryTypes ( toQualType, toQualTypes, toQualPredType, toConstrType
                       , toMethodType )

import Base.Kinds
import Base.Messages
import Base.TopEnv
import Base.Types
import Base.TypeSubst

import Env.Class
import Env.Instance
import Env.Interface
import Env.ModuleAlias (importAliases, initAliasEnv)
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

import CompilerEnv

importModules :: Monad m => Module a -> InterfaceEnv -> [ImportDecl]
              -> CYT m CompilerEnv
importModules mdl@(Module _ _ _ mid _ _ _) iEnv expImps
  = ok $ foldl importModule initEnv expImps
  where
    initEnv = (initCompilerEnv mid)
      { aliasEnv     = importAliases expImps -- import module aliases
      , interfaceEnv = iEnv                  -- imported interfaces
      , extensions   = knownExtensions mdl
      }
    importModule env (ImportDecl _ m q asM is) =
      case Map.lookup m iEnv of
        Just intf -> importInterface (fromMaybe m asM) q is intf env
        Nothing   -> internalError $ "Imports.importModules: no interface for "
                                     ++ show m

-- |The function 'importInterfaces' brings the declarations of all
-- imported interfaces into scope for the current 'Interface'.
importInterfaces :: Interface -> InterfaceEnv -> CompilerEnv
importInterfaces (Interface m is _) iEnv
  = importUnifyData $ foldl importModule initEnv is
  where
    initEnv = (initCompilerEnv m) { aliasEnv = initAliasEnv, interfaceEnv = iEnv }
    importModule env (IImportDecl _ i) = case Map.lookup i iEnv of
      Just intf -> importInterfaceIntf intf env
      Nothing   -> internalError $ "Imports.importInterfaces: no interface for "
                                   ++ show m

-- ---------------------------------------------------------------------------
-- Importing an interface into the module
-- ---------------------------------------------------------------------------

-- Four kinds of environments are computed from the interface:
--
-- 1. The operator precedences
-- 2. The type constructors
-- 3. The types of the data constructors and functions (values)
-- 4. The instances
--
-- Note that the original names of all entities defined in the imported module
-- are qualified appropriately. The same is true for type expressions.

-- When an interface is imported, the compiler first transforms the
-- interface into these environments. If an import specification is
-- present, the environments are restricted to only those entities which
-- are included in the specification or not hidden by it, respectively.
-- The resulting environments are then imported into the current module
-- using either a qualified import (if the module is imported qualified)
-- or both a qualified and an unqualified import (non-qualified import).
-- Regardless of the type of import, all instance declarations are always
-- imported into the current module.

importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec -> Interface
                -> CompilerEnv -> CompilerEnv
importInterface m q is (Interface mid _ ds) env = env'
  where
  env' = env
    { opPrecEnv = importEntities (precs  mid) m q vs id              ds $ opPrecEnv env
    , tyConsEnv = importEntities (types  mid) m q ts (importData vs) ds $ tyConsEnv env
    , valueEnv  = importEntities (values mid) m q vs id              ds $ valueEnv  env
    , classEnv  = importClasses   mid                                ds $ classEnv  env
    , instEnv   = importInstances mid                                ds $ instEnv   env
    }
  ts = isVisible addType  is
  vs = isVisible addValue is

addType :: Import -> [Ident] -> [Ident]
addType (Import            _ _) tcs = tcs
addType (ImportTypeWith _ tc _) tcs = tc : tcs
addType (ImportTypeAll     _ _) _   = internalError "Imports.addType"

addValue :: Import -> [Ident] -> [Ident]
addValue (Import            _ f) fs = f : fs
addValue (ImportTypeWith _ _ cs) fs = cs ++ fs
addValue (ImportTypeAll     _ _) _  = internalError "Imports.addValue"

isVisible :: (Import -> [Ident] -> [Ident]) -> Maybe ImportSpec
          -> Ident -> Bool
isVisible _   Nothing                 = const True
isVisible add (Just (Importing _ xs)) = (`Set.member`    Set.fromList (foldr add [] xs))
isVisible add (Just (Hiding    _ xs)) = (`Set.notMember` Set.fromList (foldr add [] xs))

importEntities :: Entity a => (IDecl -> [a]) -> ModuleIdent -> Bool
               -> (Ident -> Bool) -> (a -> a) -> [IDecl] -> TopEnv a -> TopEnv a
importEntities ents m q isVisible' f ds env =
  foldr (uncurry (if q then qualImportTopEnv m else importUnqual m)) env
        [ (x, f y) | y <- concatMap ents ds
        , let x = unqualify (origName y), isVisible' x
        ]
  where importUnqual m' x y = importTopEnv m' x y . qualImportTopEnv m' x y

importData :: (Ident -> Bool) -> TypeInfo -> TypeInfo
importData isVisible' (DataType tc k cs) =
  DataType tc k $ catMaybes $ map (importConstr isVisible') cs
importData isVisible' (RenamingType tc k nc) =
  maybe (DataType tc k []) (RenamingType tc k) (importConstr isVisible' nc)
importData _ (AliasType tc k n ty) = AliasType tc k n ty
importData isVisible' (TypeClass qcls k ms) =
  TypeClass qcls k $ catMaybes $ map (importMethod isVisible') ms
importData _ (TypeVar _) = internalError "Imports.importData: type variable"

importConstr :: (Ident -> Bool) -> DataConstr -> Maybe DataConstr
importConstr isVisible' dc
  | isVisible' (constrIdent dc) = Just dc
  | otherwise                   = Nothing

importMethod :: (Ident -> Bool) -> ClassMethod -> Maybe ClassMethod
importMethod isVisible' mthd
  | isVisible' (methodName mthd) = Just mthd
  | otherwise                    = Nothing

importClasses :: ModuleIdent -> [IDecl] -> ClassEnv -> ClassEnv
importClasses m = flip $ foldr (bindClass m)

bindClass :: ModuleIdent -> IDecl -> ClassEnv -> ClassEnv
bindClass m (HidingClassDecl p cx cls k tv) =
  bindClass m (IClassDecl p cx cls k tv [] [])
bindClass m (IClassDecl _ cx cls _ _ ds _ ) =
  bindClassInfo (qualQualify m cls) (sclss, ms)
  where sclss = map (\(Constraint _ scls _) -> qualQualify m scls) cx
        ms = map (\d -> (imethod d, isJust $ imethodArity d)) ds
bindClass _ _ = id

importInstances :: ModuleIdent -> [IDecl] -> InstEnv -> InstEnv
importInstances m = flip $ foldr (bindInstance m)

bindInstance :: ModuleIdent -> IDecl -> InstEnv -> InstEnv
bindInstance m (IInstanceDecl _ cx qcls ty is mm) = bindInstInfo
  (qualQualify m qcls, qualifyTC m $ typeConstr ty) (fromMaybe m mm, ps, is)
  where PredType ps _ = toQualPredType m [] $ QualTypeExpr NoSpanInfo cx ty
bindInstance _ _ = id

-- ---------------------------------------------------------------------------
-- Building the initial environment
-- ---------------------------------------------------------------------------

-- In a first step, the four export environments are initialized from
-- the interface's declarations.

-- operator precedences
precs :: ModuleIdent -> IDecl -> [PrecInfo]
precs m (IInfixDecl _ fix prec op) = [PrecInfo (qualQualify m op) (OpPrec fix prec)]
precs _ _                          = []

hiddenTypes :: ModuleIdent -> IDecl -> [TypeInfo]
hiddenTypes m (HidingDataDecl     _ tc k tvs) = [typeCon DataType m tc k tvs []]
hiddenTypes m (HidingClassDecl  _ _ qcls k _) = [typeCls m qcls k []]
hiddenTypes m d                               = types m d

-- type constructors and type classes
types :: ModuleIdent -> IDecl -> [TypeInfo]
types m (IDataDecl _ tc k tvs cs _) =
  [typeCon DataType m tc k tvs (map mkData cs)]
  where
    mkData (ConstrDecl _ c tys) =
      DataConstr c (toQualTypes m tvs tys)
    mkData (ConOpDecl _  ty1 c ty2) =
      DataConstr c (toQualTypes m tvs [ty1, ty2])
    mkData (RecordDecl _ c fs) =
      RecordConstr c labels (toQualTypes m tvs tys)
      where (labels, tys) = unzip [(l, ty) | FieldDecl _ ls ty <- fs, l <- ls]
types m (INewtypeDecl _ tc k tvs nc _) =
  [typeCon RenamingType m tc k tvs (mkData nc)]
  where
    mkData (NewConstrDecl _ c ty) =
      DataConstr c [toQualType m tvs ty]
    mkData (NewRecordDecl _ c (l, ty)) =
      RecordConstr c [l] [toQualType m tvs ty]
types m (ITypeDecl _ tc k tvs ty) =
  [typeCon aliasType m tc k tvs (toQualType m tvs ty)]
  where
    aliasType tc' k' = AliasType tc' k' (length tvs)
types m (IClassDecl _ _ qcls k tv ds _) =
  [typeCls m qcls k (map mkMethod ds)]
  where
    mkMethod (IMethodDecl _ f a qty) = ClassMethod f a $
      qualifyPredType m $ normalize 1 $ toMethodType qcls tv qty
types _ _ = []

-- type constructors
typeCon :: (QualIdent -> Kind -> a) -> ModuleIdent -> QualIdent
        -> Maybe KindExpr -> [Ident] -> a
typeCon f m tc k tvs = f (qualQualify m tc) (toKind' k (length tvs))

-- type classes
typeCls :: ModuleIdent -> QualIdent -> Maybe KindExpr -> [ClassMethod]
        -> TypeInfo
typeCls m qcls k ms = TypeClass (qualQualify m qcls) (toKind' k 0) ms

-- data constructors, record labels, functions and class methods
values :: ModuleIdent -> IDecl -> [ValueInfo]
values m (IDataDecl _ tc _ tvs cs hs) =
  map (dataConstr m tc' tvs)
      (filter ((\con -> con `notElem` hs || isHiddenButNeeded con)
              . constrId) cs) ++
  map (recLabel m tc' tvs ty') (nubBy sameLabel clabels)
  where tc' = qualQualify m tc
        ty' = constrType tc' tvs
        labels   = [ (l, lty) | RecordDecl _ _ fs <- cs
                   , FieldDecl _ ls lty <- fs, l <- ls, l `notElem` hs
                   ]
        clabels  = [(l, constr l, ty) | (l, ty) <- labels]
        constr l = [constrId c | c <- cs, l `elem` recordLabels c]
        -- hidden constructors needed for record updates with visible labels
        hiddenCs = [c | (l, _) <- labels, c <- constr l, c `elem` hs]
        isHiddenButNeeded = flip elem hiddenCs
        sameLabel (l1,_,_) (l2,_,_) = l1 == l2
values m (INewtypeDecl _ tc _ tvs nc hs) =
  map (newConstr m tc' tvs) [nc | nconstrId nc `notElem` hs] ++
  case nc of
    NewConstrDecl _ _ _        -> []
    NewRecordDecl _ c (l, lty) ->
      [recLabel m tc' tvs ty' (l, [c], lty) | l `notElem` hs]
  where tc' = qualQualify m tc
        ty' = constrType tc' tvs
values m (IFunctionDecl _ f Nothing a qty) =
  [Value (qualQualify m f) Nothing a (typeScheme (toQualPredType m [] qty))]
values m (IFunctionDecl _ f (Just tv) _ qty) =
  let mcls = case qty of
        QualTypeExpr _ ctx _ -> fmap (\(Constraint _ qcls _) -> qcls) $
                                find (\(Constraint _ _ ty) -> isVar ty) ctx
        _                    -> Nothing
  in [Value (qualQualify m f) mcls 0 (typeScheme (toQualPredType m [tv] qty))]
  where
    isVar (VariableType _ i) = i == tv
    isVar _                  = False
values m (IClassDecl _ _ qcls _ tv ds hs) =
  map (classMethod m qcls' tv hs) ds
  where qcls' = qualQualify m qcls
values _ _                        = []

dataConstr :: ModuleIdent -> QualIdent -> [Ident] -> ConstrDecl -> ValueInfo
dataConstr m tc tvs (ConstrDecl _ c tys) =
  DataConstructor (qualifyLike tc c) a labels $
    constrType' m tc tvs tys
  where a      = length tys
        labels = replicate a anonId
dataConstr m tc tvs (ConOpDecl _ ty1 op ty2) =
  DataConstructor (qualifyLike tc op) 2 [anonId, anonId] $
    constrType' m tc tvs [ty1, ty2]
dataConstr m tc tvs (RecordDecl _ c fs) =
  DataConstructor (qualifyLike tc c) a labels $
    constrType' m tc tvs tys
  where fields        = [(l, ty) | FieldDecl _ ls ty <- fs, l <- ls]
        (labels, tys) = unzip fields
        a             = length labels

newConstr :: ModuleIdent -> QualIdent -> [Ident] -> NewConstrDecl -> ValueInfo
newConstr m tc tvs (NewConstrDecl _ c ty1) =
  NewtypeConstructor (qualifyLike tc c) anonId $
  constrType' m tc tvs [ty1]
newConstr m tc tvs (NewRecordDecl _ c (l, ty1)) =
  NewtypeConstructor (qualifyLike tc c) l $
  constrType' m tc tvs [ty1]

recLabel :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr
           -> (Ident, [Ident], TypeExpr) -> ValueInfo
recLabel m tc tvs ty0 (l, cs, lty) = Label ql qcs tySc
  where ql   = qualifyLike tc l
        qcs  = map (qualifyLike tc) cs
        tySc = polyType (toQualType m tvs (ArrowType NoSpanInfo ty0 lty))

constrType' :: ModuleIdent -> QualIdent -> [Ident] -> [TypeExpr] -> TypeScheme
constrType' m tc tvs tys = ForAll (length tvs) pty
  where pty  = qualifyPredType m $ toConstrType tc tvs tys

constrType :: QualIdent -> [Ident] -> TypeExpr
constrType tc tvs = foldl (ApplyType NoSpanInfo) (ConstructorType NoSpanInfo tc)
                      $ map (VariableType NoSpanInfo) tvs

-- We always enter class methods with an arity of 0 into the value environment
-- because there may be different implementations with different arities.

classMethod :: ModuleIdent -> QualIdent -> Ident -> [Ident] -> IMethodDecl
            -> ValueInfo
classMethod m qcls tv hs (IMethodDecl _ f _ qty) =
  Value (qualifyLike qcls f) mcls 0 $
    typeScheme $ qualifyPredType m $ toMethodType qcls tv qty
  where
    mcls = if f `elem` hs then Nothing else Just qcls

-- ---------------------------------------------------------------------------

-- After all modules have been imported, the compiler has to ensure that
-- all references to a data type use the same list of constructors.

importUnifyData :: CompilerEnv -> CompilerEnv
importUnifyData cEnv = cEnv { tyConsEnv = importUnifyData' $ tyConsEnv cEnv }

importUnifyData' :: TCEnv -> TCEnv
importUnifyData' tcEnv = fmap (setInfo allTyCons) tcEnv
  where
  setInfo tcs t   = case Map.lookup (origName t) tcs of
                         Nothing -> error "Imports.importUnifyData'"
                         Just ty -> ty
  allTyCons       = foldr (mergeData . snd) Map.empty $ allImports tcEnv
  mergeData t tcs =
    Map.insert tc (maybe t (sureMerge t) $ Map.lookup tc tcs) tcs
    where tc = origName t
  sureMerge x y = case merge x y of
                       Nothing -> error "Imports.importUnifyData'.sureMerge"
                       Just z  -> z

-- ---------------------------------------------------------------------------

-- |
qualifyEnv :: CompilerEnv -> CompilerEnv
qualifyEnv env = qualifyLocal env
               $ foldl (flip importInterfaceIntf) initEnv
               $ Map.elems
               $ interfaceEnv env
  where initEnv = initCompilerEnv $ moduleIdent env

qualifyLocal :: CompilerEnv -> CompilerEnv -> CompilerEnv
qualifyLocal currentEnv initEnv = currentEnv
  { opPrecEnv = foldr bindQual   pEnv  $ localBindings $ opPrecEnv currentEnv
  , tyConsEnv = foldr bindQual   tcEnv $ localBindings $ tyConsEnv currentEnv
  , valueEnv  = foldr bindGlobal tyEnv $ localBindings $ valueEnv  currentEnv
  , classEnv  = Map.unionWith mergeClassInfo clsEnv $ classEnv currentEnv
  , instEnv   = Map.union                    iEnv   $ instEnv  currentEnv
  }
  where
    pEnv   = opPrecEnv initEnv
    tcEnv  = tyConsEnv initEnv
    tyEnv  = valueEnv  initEnv
    clsEnv = classEnv  initEnv
    iEnv   = instEnv   initEnv
    bindQual   (_, y) = qualBindTopEnv (origName y) y
    bindGlobal (x, y)
      | hasGlobalScope x = bindQual (x, y)
      | otherwise        = bindTopEnv x y

-- Importing an interface into another interface is somewhat simpler
-- because all entities are imported into the environment. In addition,
-- only a qualified import is necessary. Note that the hidden data types
-- are imported as well because they may be used in type expressions in
-- an interface.

importInterfaceIntf :: Interface -> CompilerEnv -> CompilerEnv
importInterfaceIntf (Interface m _ ds) env = env
  { opPrecEnv = importEntitiesIntf m (precs  m)       ds $ opPrecEnv env
  , tyConsEnv = importEntitiesIntf m (hiddenTypes  m) ds $ tyConsEnv env
  , valueEnv  = importEntitiesIntf m (values m)       ds $ valueEnv  env
  , classEnv  = importClasses      m                  ds $ classEnv  env
  , instEnv   = importInstances    m                  ds $ instEnv   env
  }

importEntitiesIntf :: Entity a => ModuleIdent -> (IDecl -> [a]) -> [IDecl]
                    -> TopEnv a -> TopEnv a
importEntitiesIntf m ents ds env = foldr importEntity env (concatMap ents ds)
  where importEntity x = qualImportTopEnv (fromMaybe m (qidModule (origName x)))
                                          (unqualify (origName x)) x
