{- |
  Module      :  $Header$
  Description :  Dictionary insertion
  Copyright   :  (c) 2016 - 2017 Finn Teegen
  License     :  BSD-3-clause

  Maintainer  :  bjp@informatik.uni-kiel.de
  Stability   :  experimental
  Portability :  portable

  TODO
-}

{-# LANGUAGE CPP #-}
module Transformations.Dictionary
  ( insertDicts
  , dictTypeId, qDictTypeId, dictConstrId, qDictConstrId
  , defaultMethodId, qDefaultMethodId, superDictStubId, qSuperDictStubId
  , instFunId, qInstFunId, implMethodId, qImplMethodId
  ) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>))
import           Data.Traversable         (traverse)
#endif
import           Control.Monad.Extra      ( concatMapM, liftM, maybeM, when
                                          , zipWithM )
import qualified Control.Monad.State as S (State, runState, gets, modify)

import           Data.List         (inits, nub, partition, tails, zipWith4)
import qualified Data.Map   as Map (Map, empty, insert, lookup, mapWithKey)
import           Data.Maybe        (fromMaybe, isJust)
import qualified Data.Set   as Set ( deleteMin, lookupMin, null, size, toAscList
                                   , toList, union )

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Syntax

import Base.CurryKinds
import Base.CurryTypes
import Base.Expr
import Base.Kinds
import Base.Messages (internalError)
import Base.TopEnv
import Base.Types
import Base.TypeSubst
import Base.Typing
import Base.Utils (uncurry3)

import Env.Class
import Env.Instance
import Env.Interface
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

data DTState = DTState
  { moduleIdent :: ModuleIdent
  , tyConsEnv   :: TCEnv
  , valueEnv    :: ValueEnv
  , classEnv    :: ClassEnv
  , instEnv     :: InstEnv
  , opPrecEnv   :: OpPrecEnv
  , dictEnv     :: DictEnv    -- for dictionary insertion
  , specEnv     :: SpecEnv    -- for dictionary specialization
  , nextId      :: Integer
  }

type DTM = S.State DTState

insertDicts :: Bool -> InterfaceEnv -> TCEnv -> ValueEnv -> ClassEnv
            -> InstEnv -> OpPrecEnv -> Module PredType
            -> (Module Type, InterfaceEnv, TCEnv, ValueEnv, OpPrecEnv)
insertDicts inlDi intfEnv tcEnv vEnv clsEnv inEnv pEnv mdl@(Module _ _ _ m _ _ _) =
  (mdl', intfEnv', tcEnv', vEnv', pEnv')
  where initState =
          DTState m tcEnv vEnv clsEnv inEnv pEnv emptyDictEnv emptySpEnv 1
        (mdl', tcEnv', vEnv', pEnv') =
          runDTM (dictTrans mdl >>= (if inlDi then specialize else return) >>= cleanup) initState
        intfEnv' = dictTransInterfaces vEnv' clsEnv intfEnv

runDTM :: DTM a -> DTState -> (a, TCEnv, ValueEnv, OpPrecEnv)
runDTM dtm s =
  let (a, s') = S.runState dtm s in (a, tyConsEnv s', valueEnv s', opPrecEnv s')

getModuleIdent :: DTM ModuleIdent
getModuleIdent = S.gets moduleIdent

getTyConsEnv :: DTM TCEnv
getTyConsEnv = S.gets tyConsEnv

modifyTyConsEnv :: (TCEnv -> TCEnv) -> DTM ()
modifyTyConsEnv f = S.modify $ \s -> s { tyConsEnv = f $ tyConsEnv s }

getValueEnv :: DTM ValueEnv
getValueEnv = S.gets valueEnv

modifyValueEnv :: (ValueEnv -> ValueEnv) -> DTM ()
modifyValueEnv f = S.modify $ \s -> s { valueEnv = f $ valueEnv s }

withLocalValueEnv :: DTM a -> DTM a
withLocalValueEnv act = do
  oldEnv <- getValueEnv
  res <- act
  modifyValueEnv $ const oldEnv
  return res

getClassEnv :: DTM ClassEnv
getClassEnv = S.gets classEnv

getInstEnv :: DTM InstEnv
getInstEnv = S.gets instEnv

modifyInstEnv :: (InstEnv -> InstEnv) -> DTM ()
modifyInstEnv f = S.modify $ \s -> s { instEnv = f $ instEnv s }

getPrecEnv :: DTM OpPrecEnv
getPrecEnv = S.gets opPrecEnv

modifyPrecEnv :: (OpPrecEnv -> OpPrecEnv) -> DTM ()
modifyPrecEnv f = S.modify $ \s -> s { opPrecEnv = f $ opPrecEnv s }

getDictEnv :: DTM DictEnv
getDictEnv = S.gets dictEnv

modifyDictEnv :: (DictEnv -> DictEnv) -> DTM ()
modifyDictEnv f = S.modify $ \s -> s { dictEnv = f $ dictEnv s }

withLocalDictEnv :: DTM a -> DTM a
withLocalDictEnv act = do
  oldEnv <- getDictEnv
  res <- act
  modifyDictEnv $ const oldEnv
  return res

getSpEnv :: DTM SpecEnv
getSpEnv = S.gets specEnv

setSpEnv :: SpecEnv -> DTM ()
setSpEnv spEnv = S.modify $ \s -> s { specEnv = spEnv }

getNextId :: DTM Integer
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

-- -----------------------------------------------------------------------------
-- Lifting class and instance declarations
-- -----------------------------------------------------------------------------

-- When we lift class and instance declarations, we can remove the optional
-- default declaration since it has already been considered during the type
-- check.

liftDecls :: Decl PredType -> DTM [Decl PredType]
liftDecls (DefaultDecl _ _) = return []
liftDecls (ClassDecl _ _ _ cls tvs ds) = do
  m <- getModuleIdent
  liftClassDecls (qualifyWith m cls) tvs ds
liftDecls (InstanceDecl _ _ cx cls tys ds) = do
  clsEnv <- getClassEnv
  let PredTypes ps tys' = toPredTypes [] OPred cx tys
      ps' = minPredSet clsEnv ps
  liftInstanceDecls ps' cls tys' ds
liftDecls d = return [d]

liftClassDecls :: QualIdent -> [Ident] -> [Decl PredType] -> DTM [Decl PredType]
liftClassDecls cls tvs ds = do
  dictDecl <- createClassDictDecl cls tvs ods
  clsEnv <- getClassEnv
  let fs = classMethods cls clsEnv
  methodDecls <- mapM (createClassMethodDecl cls ms) fs
  return $ dictDecl : methodDecls
  where (vds, ods) = partition isValueDecl ds
        ms = methodMap vds

liftInstanceDecls :: PredSet -> QualIdent -> [Type] -> [Decl PredType]
                  -> DTM [Decl PredType]
liftInstanceDecls ps cls tys ds = do
  dictDecl <- createInstDictDecl ps cls tys
  clsEnv <- getClassEnv
  let fs = classMethods cls clsEnv
  methodDecls <- mapM (createInstMethodDecl ps cls tys ms) fs
  return $ dictDecl : methodDecls
  where ms = methodMap ds

-- Since not every class method needs to be implemented in a class or instance
-- declaration, we use a map to associate a class method identifier with its
-- implementation.

type MethodMap = [(Ident, Decl PredType)]

-- We have to unrename the method's identifiers here because the syntax check
-- has renamed them before.

methodMap :: [Decl PredType] -> MethodMap
methodMap ds = [(unRenameIdent f, d) | d@(FunctionDecl _ _ f _) <- ds]

createClassDictDecl :: QualIdent -> [Ident] -> [Decl a] -> DTM (Decl a)
createClassDictDecl cls tvs ds = do
  c <- createClassDictConstrDecl cls tvs ds
  return $ DataDecl NoSpanInfo (dictTypeId cls) tvs [c] []

createClassDictConstrDecl :: QualIdent -> [Ident] -> [Decl a] -> DTM ConstrDecl
createClassDictConstrDecl cls tvs ds = do
  let tvs' = tvs ++ filter (`notElem` map unRenameIdent tvs) identSupply
      mtys = map (fromType tvs' . generalizeMethodType . transformMethodPredType)
                 [toMethodType cls tvs qty | TypeSig _ fs qty <- ds, _ <- fs]
  return $ ConstrDecl NoSpanInfo (dictConstrId cls) mtys

classDictConstrPredType :: ValueEnv -> ClassEnv -> QualIdent -> PredType
classDictConstrPredType vEnv clsEnv cls =
  PredType ps $ foldr TypeArrow ty mtys
 where
  varTys = map TypeVariable [0 .. classArity cls clsEnv - 1]
  ps     = superClasses cls clsEnv
  fs     = classMethods cls clsEnv
  mptys  = map (classMethodType vEnv cls) fs
  ty     = dictType $ Pred OPred cls varTys
  mtys   = map (generalizeMethodType . transformMethodPredType) mptys

createInstDictDecl :: PredSet -> QualIdent -> [Type] -> DTM (Decl PredType)
createInstDictDecl ps cls tys = do
  pty <- PredType ps . arrowBase <$> getInstDictConstrType cls tys
  funDecl NoSpanInfo pty (instFunId cls tys)
    [ConstructorPattern NoSpanInfo predUnitType qUnitId []]
    <$> createInstDictExpr cls tys

createInstDictExpr :: QualIdent -> [Type] -> DTM (Expression PredType)
createInstDictExpr cls tys = do
  ty <- instType <$> getInstDictConstrType cls tys
  m <- getModuleIdent
  clsEnv <- getClassEnv
  let fs = map (qImplMethodId m cls tys) $ classMethods cls clsEnv
  return $ apply (Constructor NoSpanInfo (predType ty) (qDictConstrId cls))
             (zipWith (Variable NoSpanInfo . predType) (arrowArgs ty) fs)

getInstDictConstrType :: QualIdent -> [Type] -> DTM Type
getInstDictConstrType cls tys = do
  vEnv <- getValueEnv
  clsEnv <- getClassEnv
  return $ instanceTypes tys $ unpredType $
    classDictConstrPredType vEnv clsEnv cls

createClassMethodDecl :: QualIdent -> MethodMap -> Ident -> DTM (Decl PredType)
createClassMethodDecl cls =
  createMethodDecl (defaultMethodId cls) (defaultClassMethodDecl cls)

defaultClassMethodDecl :: QualIdent -> Ident -> DTM (Decl PredType)
defaultClassMethodDecl cls f = do
  pty@(PredType _ ty) <- getClassMethodType cls f
  return $ funDecl NoSpanInfo pty f [] $ preludeError (instType ty) $
    "No instance or default method for class operation " ++ escName f

getClassMethodType :: QualIdent -> Ident -> DTM PredType
getClassMethodType cls f = do
  vEnv <- getValueEnv
  return $ classMethodType vEnv cls f

classMethodType :: ValueEnv -> QualIdent -> Ident -> PredType
classMethodType vEnv cls f = pty
  where ForAll _ pty = funType (qualifyLike cls f) vEnv

createInstMethodDecl :: PredSet -> QualIdent -> [Type] -> MethodMap -> Ident
                     -> DTM (Decl PredType)
createInstMethodDecl ps cls tys =
  createMethodDecl (implMethodId cls tys) (defaultInstMethodDecl ps cls tys)

defaultInstMethodDecl :: PredSet -> QualIdent -> [Type] -> Ident
                      -> DTM (Decl PredType)
defaultInstMethodDecl ps cls tys f = do
  vEnv <- getValueEnv
  let pty@(PredType _ ty) = instMethodType vEnv ps cls tys f
  return $ funDecl NoSpanInfo pty f [] $
    Variable NoSpanInfo (predType $ instType ty) (qDefaultMethodId cls f)

-- Returns the type for a given instance's method of a given class. To this
-- end, the class method's type is stripped of its first predicate (which is
-- the implicit class constraint) and the class variables are replaced with the
-- instance's types. The remaining predicate set is then united with the
-- instance's predicate set.

instMethodType :: ValueEnv -> PredSet -> QualIdent -> [Type] -> Ident
               -> PredType
instMethodType vEnv ps cls tys f = PredType (ps `Set.union` ps'') ty'
  where PredType ps'  ty  = classMethodType vEnv cls f
        PredType ps'' ty' = instanceTypes tys $ PredType (Set.deleteMin ps') ty

createMethodDecl :: (Ident -> Ident) -> (Ident -> DTM (Decl PredType))
                 -> MethodMap -> Ident -> DTM (Decl PredType)
createMethodDecl methodId defaultDecl ms f =
  liftM (renameDecl $ methodId f) $ maybe (defaultDecl f) return (lookup f ms)

-- We have to rename the left hand side of lifted function declarations
-- accordingly which is done by the function 'renameDecl'.

renameDecl :: Ident -> Decl a -> Decl a
renameDecl f (FunctionDecl p a _ eqs) = FunctionDecl p a f $ map renameEq eqs
  where renameEq (Equation p' lhs rhs) = Equation p' (renameLhs lhs) rhs
        renameLhs (FunLhs _ _ ts) = FunLhs NoSpanInfo f ts
        renameLhs _ = internalError "Dictionary.renameDecl.renameLhs"
renameDecl _ _ = internalError "Dictionary.renameDecl"

-- -----------------------------------------------------------------------------
-- Creating stub declarations
-- -----------------------------------------------------------------------------

-- For each class method f defined in the processed module we have to introduce
-- a stub method with the same name that selects the appropriate function from
-- the provided dictionary and applies the remaining arguments to it. We also
-- create a stub method for each super class selecting the corresponding super
-- class dictionary from the provided class dictionary.

createStubs :: Decl PredType -> DTM [Decl Type]
createStubs (ClassDecl _ _ _ cls _ _) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  clsEnv <- getClassEnv
  let ocls  = qualifyWith m cls
      fs    = classMethods ocls clsEnv
      sclss = Set.toAscList (superClasses ocls clsEnv)
      dictConstrPty = classDictConstrPredType vEnv clsEnv ocls
      (superDictAndMethodTys, dictTy) =
        arrowUnapply $ transformPredType dictConstrPty
      (superDictTys, methodTys)       =
        splitAt (length sclss) superDictAndMethodTys
      (superStubTys, methodStubTys)   = splitAt (length sclss) $
        map (TypeArrow dictTy) superDictAndMethodTys
  superDictVs <- mapM (freshVar "_#super" . instType) superDictTys
  methodVs <- mapM (freshVar "_#meth" . instType) methodTys
  let patternVs   = superDictVs ++ methodVs
      pattern     = createDictPattern (instType dictTy) ocls patternVs
      superStubs  = zipWith3 (createSuperDictStubDecl pattern ocls)
                      superStubTys sclss superDictVs
      methodStubs = zipWith3 (createMethodStubDecl pattern)
                      methodStubTys fs methodVs
  return $ superStubs ++ methodStubs
createStubs _ = return []

createDictPattern :: Type -> QualIdent -> [(Type, Ident)] -> Pattern Type
createDictPattern a cls = constrPattern a (qDictConstrId cls)

createSuperDictStubDecl :: Pattern Type -> QualIdent -> Type -> Pred
                        -> (Type, Ident) -> Decl Type
createSuperDictStubDecl t cls a sclsPred v =
  createStubDecl t a (superDictStubId cls sclsPred) v

createMethodStubDecl :: Pattern Type -> Type -> Ident -> (Type, Ident) -> Decl Type
createMethodStubDecl = createStubDecl

createStubDecl :: Pattern Type -> Type -> Ident -> (Type, Ident) -> Decl Type
createStubDecl t a f v =
  FunctionDecl NoSpanInfo a f [createStubEquation t f v]

createStubEquation :: Pattern Type -> Ident -> (Type, Ident) -> Equation Type
createStubEquation t f v = 
  mkEquation NoSpanInfo f [VariablePattern NoSpanInfo (TypeArrow unitType (typeOf t)) (mkIdent "_#temp")] $
    mkLet [FunctionDecl NoSpanInfo (TypeArrow (typeOf t) (fst v)) (mkIdent "_#lambda")
      [mkEquation NoSpanInfo (mkIdent "_#lambda") [t] $ uncurry mkVar v]]
      (apply (Variable NoSpanInfo (TypeArrow (typeOf t) (fst v)) (qualify $ mkIdent "_#lambda"))
        [apply (Variable NoSpanInfo (TypeArrow unitType (typeOf t)) (qualify $ mkIdent "_#temp"))
          [Constructor NoSpanInfo unitType qUnitId]])

superDictStubType :: QualIdent -> Pred -> [Type] -> Type
superDictStubType cls sclsPred tys = TypeArrow (rtDictType $ Pred OPred cls tys)
  (rtDictType $ expandAliasType tys sclsPred)

-- -----------------------------------------------------------------------------
-- Entering new bindings into the environments
-- -----------------------------------------------------------------------------

bindDictTypes :: ModuleIdent -> ClassEnv -> TCEnv -> TCEnv
bindDictTypes m clsEnv tcEnv =
  foldr (bindDictType m clsEnv) tcEnv (allEntities tcEnv)

bindDictType :: ModuleIdent -> ClassEnv -> TypeInfo -> TCEnv -> TCEnv
bindDictType m clsEnv (TypeClass cls k ms) = bindEntity m tc ti
 where
  ti  = DataType tc (dictTypeKind cls k) [c]
  tc  = qDictTypeId cls
  c   = DataConstr (dictConstrId cls) (map rtDictType (Set.toAscList ps) ++ tys)
  ps  = superClasses cls clsEnv
  tys = map (generalizeMethodType . transformMethodPredType . methodType) ms
bindDictType _ _      _                     = id

bindClassDecls :: ModuleIdent -> TCEnv -> ClassEnv -> ValueEnv -> ValueEnv
bindClassDecls m tcEnv clsEnv =
  flip (foldr $ bindClassEntities m clsEnv) $ allEntities tcEnv

-- It is safe to use 'fromMaybe 0' in 'bindClassEntities', because the
-- augmentation has already replaced the 'Nothing' value for the arity
-- of a method's implementation with 'Just 1' (despite the fact that
-- maybe no default implementation has been provided) if the method has
-- been augmented.

bindClassEntities :: ModuleIdent -> ClassEnv -> TypeInfo -> ValueEnv -> ValueEnv
bindClassEntities m clsEnv (TypeClass cls _ ms) =
  bindClassDict m clsEnv cls . bindSuperStubs m clsEnv cls sclss .
    bindDefaultMethods m cls fs
  where fs    = zip (map methodName ms) (map (fromMaybe 0 . methodArity) ms)
        sclss = superClasses cls clsEnv
bindClassEntities _ _ _ = id

bindClassDict :: ModuleIdent -> ClassEnv -> QualIdent -> ValueEnv -> ValueEnv
bindClassDict m clsEnv cls vEnv = bindEntity m c dc vEnv
  where c  = qDictConstrId cls
        dc = DataConstructor c a (replicate a anonId) tySc
        a  = Set.size ps + arrowArity ty
        pty@(PredType ps ty) = classDictConstrPredType vEnv clsEnv cls
        tySc = ForAll (classArity cls clsEnv) pty

bindDefaultMethods :: ModuleIdent -> QualIdent -> [(Ident, Int)] -> ValueEnv
                   -> ValueEnv
bindDefaultMethods m = flip . foldr . bindDefaultMethod m

-- TODO: Should the implicit class constraint of a default method implementation
--         be marked as such?
bindDefaultMethod :: ModuleIdent -> QualIdent -> (Ident, Int) -> ValueEnv
                  -> ValueEnv
bindDefaultMethod m cls (f, n) vEnv =
  bindMethod m (qDefaultMethodId cls f) n (classMethodType vEnv cls f) vEnv

bindSuperStubs :: ModuleIdent -> ClassEnv -> QualIdent -> PredSet -> ValueEnv
               -> ValueEnv
bindSuperStubs m clsEnv = flip . foldr . bindSuperStub m clsEnv

bindSuperStub :: ModuleIdent -> ClassEnv -> QualIdent -> Pred -> ValueEnv -> ValueEnv
bindSuperStub m clsEnv cls sclsPred =
  bindEntity m f $ Value f Nothing 1 $ polyType ty
  where f  = qSuperDictStubId cls sclsPred
        ar = classArity cls clsEnv
        ty = superDictStubType cls sclsPred (map TypeVariable [0 .. ar])

bindInstDecls :: ModuleIdent -> ClassEnv -> InstEnv -> ValueEnv -> ValueEnv
bindInstDecls m clsEnv = flip (foldr $ bindInstFuns m clsEnv) . instEnvList

bindInstFuns :: ModuleIdent -> ClassEnv -> (InstIdent, InstInfo) -> ValueEnv
             -> ValueEnv
bindInstFuns m clsEnv ((cls, tys), (m', ps, is)) =
  bindInstDict m cls tys m' ps . bindInstMethods m clsEnv cls tys m' ps is

bindInstDict :: ModuleIdent -> QualIdent -> [Type] -> ModuleIdent -> PredSet
             -> ValueEnv -> ValueEnv
bindInstDict m cls tys m' ps = bindMethod m (qInstFunId m' cls tys) 1 $
  PredType ps $ rtDictType $ Pred OPred cls tys

bindInstMethods :: ModuleIdent -> ClassEnv -> QualIdent -> [Type] -> ModuleIdent
                -> PredSet -> [(Ident, Int)] -> ValueEnv -> ValueEnv
bindInstMethods m clsEnv cls tys m' ps is =
  flip (foldr (bindInstMethod m cls tys m' ps is)) (classMethods cls clsEnv)

bindInstMethod :: ModuleIdent -> QualIdent -> [Type] -> ModuleIdent
               -> PredSet -> [(Ident, Int)] -> Ident -> ValueEnv -> ValueEnv
bindInstMethod m cls tys m' ps is f vEnv = bindMethod m f' a pty vEnv
  where f'  = qImplMethodId m' cls tys f
        a   = fromMaybe 0 $ lookup f is
        pty = instMethodType vEnv ps cls tys f

bindMethod :: ModuleIdent -> QualIdent -> Int -> PredType -> ValueEnv
           -> ValueEnv
bindMethod m f n pty = bindEntity m f $ Value f Nothing n $ typeScheme pty

-- The function 'bindEntity' introduces a binding for an entity into a top-level
-- environment. Depending on whether the entity is defined in the current module
-- or not, either an unqualified and a qualified local binding or a qualified
-- import are added to the environment.

bindEntity :: Entity a => ModuleIdent -> QualIdent -> a -> TopEnv a
           -> TopEnv a
bindEntity m x = case qidModule (qualUnqualify m x) of
  Just m' | m /= m' -> qualImportTopEnv m' x'
  _                 -> qualBindTopEnv (qualifyWith m x')
  where x' = unqualify x

-- -----------------------------------------------------------------------------
-- Transforming the environments
-- -----------------------------------------------------------------------------

dictTransTypes :: TCEnv -> TCEnv
dictTransTypes = fmap dictTransTypeInfo

dictTransTypeInfo :: TypeInfo -> TypeInfo
dictTransTypeInfo (DataType tc k cs) =
  DataType tc k $ map dictTransDataConstr cs
dictTransTypeInfo (RenamingType tc k nc) =
  RenamingType tc k $ dictTransDataConstr nc
dictTransTypeInfo ti@(AliasType _ _ _ _) = ti
dictTransTypeInfo (TypeClass cls k ms) =
  TypeClass cls k $ map dictTransClassMethod ms
dictTransTypeInfo (TypeVar _) =
  internalError "Dictionary.dictTransTypeInfo: type variable"

dictTransDataConstr :: DataConstr -> DataConstr
dictTransDataConstr (DataConstr c tys) = DataConstr c tys
dictTransDataConstr (RecordConstr c _ tys) =
  dictTransDataConstr $ DataConstr c tys

-- For the same reason as in 'bindClassEntities' it is safe to use 'fromMaybe 0'
-- in 'dictTransClassMethod'. Note that type classes are removed anyway in the
-- cleanup phase.

dictTransClassMethod :: ClassMethod -> ClassMethod
dictTransClassMethod (ClassMethod f a pty) = ClassMethod f a' $ predType ty
  where a' = Just $ fromMaybe 0 a + arrowArity ty - arrowArity (unpredType pty)
        ty = transformPredType pty

dictTransValues :: ValueEnv -> ValueEnv
dictTransValues = fmap dictTransValueInfo

dictTransValueInfo :: ValueInfo -> ValueInfo
dictTransValueInfo (DataConstructor c a ls (ForAll n pty)) =
  DataConstructor c a' ls' $ ForAll n $ predType ty
  where a'  = arrowArity ty
        ls' = replicate (a' - a) anonId ++ ls
        ty  = transformPredType pty
dictTransValueInfo (NewtypeConstructor c l (ForAll n pty)) =
  NewtypeConstructor c l (ForAll n (predType (unpredType pty)))
dictTransValueInfo (Value f cm a (ForAll n pty)) =
  Value f Nothing a' $ ForAll n $ predType ty
  where a' = a + if isJust cm then 1 else arrowArity ty - arrowArity (unpredType pty)
        ty = transformPredType pty
dictTransValueInfo (Label l cs (ForAll n pty)) =
  Label l cs $ ForAll n $ predType $ unpredType pty

-- -----------------------------------------------------------------------------
-- Adding exports
-- -----------------------------------------------------------------------------

addExports :: Maybe ExportSpec -> [Export] -> Maybe ExportSpec
addExports (Just (Exporting p es)) es' = Just $ Exporting p $ es ++ es'
addExports Nothing                 _   = internalError "Dictionary.addExports"

dictExports :: Decl a -> DTM [Export]
dictExports (ClassDecl _ _ _ cls _ _) = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  return $ classExports m clsEnv cls
dictExports (InstanceDecl _ _ _ cls tys _) = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  return $ instExports m clsEnv cls (toTypes [] tys)
dictExports _ = return []

classExports :: ModuleIdent -> ClassEnv -> Ident -> [Export]
classExports m clsEnv cls =
  ExportTypeWith NoSpanInfo (qDictTypeId qcls) [dictConstrId qcls] :
   map (Export NoSpanInfo . qSuperDictStubId qcls) sclss ++
     map (Export NoSpanInfo . qDefaultMethodId qcls) (classMethods qcls clsEnv)
  where qcls  = qualifyWith m cls
        sclss = Set.toAscList (superClasses qcls clsEnv)

instExports :: ModuleIdent -> ClassEnv -> QualIdent -> [Type] -> [Export]
instExports m clsEnv cls tys =
  Export NoSpanInfo (qInstFunId m cls tys) :
    map (Export NoSpanInfo . qImplMethodId m cls tys) (classMethods cls clsEnv)

-- -----------------------------------------------------------------------------
-- Transforming the module
-- -----------------------------------------------------------------------------

type DictEnv = [(Pred, Expression Type)]

emptyDictEnv :: DictEnv
emptyDictEnv = []

class DictTrans a where
  dictTrans :: a PredType -> DTM (a Type)

instance DictTrans Module where
  dictTrans (Module spi li ps m es is ds) = do
    liftedDs <- concatMapM liftDecls ds
    stubDs <- concatMapM createStubs ds
    tcEnv <- getTyConsEnv
    clsEnv <- getClassEnv
    inEnv <- getInstEnv
    modifyValueEnv $ bindClassDecls m tcEnv clsEnv
    modifyValueEnv $ bindInstDecls m clsEnv inEnv
    modifyTyConsEnv $ bindDictTypes m clsEnv
    transDs <- mapM dictTrans liftedDs
    modifyValueEnv $ dictTransValues
    modifyTyConsEnv $ dictTransTypes
    dictEs <- addExports es <$> concatMapM dictExports ds
    return $ Module spi li ps m dictEs is $ transDs ++ stubDs

-- We use and transform the type from the type constructor environment for
-- transforming a constructor declaration as it contains the reduced and
-- restricted predicate set for each data constructor.

-- The pattern declaration case of the DictTrans Decl instance converts
-- variable declarations with an overloaded type into function declarations.
-- This is necessary so that the compiler can add the implicit dictionary
-- arguments to the declaration.

instance DictTrans Decl where
  dictTrans (InfixDecl      p fix prec ops) = return $ InfixDecl p fix prec ops
  dictTrans (DataDecl        p tc tvs cs _) = do
    m <- getModuleIdent
    tcEnv <- getTyConsEnv
    let DataType _ _ cs' = head $ qualLookupTypeInfo (qualifyWith m tc) tcEnv
    return $ DataDecl p tc tvs (zipWith (dictTransConstrDecl tvs) cs cs') []
  dictTrans (ExternalDataDecl     p tc tvs) = return $ ExternalDataDecl p tc tvs
  dictTrans (NewtypeDecl     p tc tvs nc _) =
    return $ NewtypeDecl p tc tvs nc []
  dictTrans (TypeDecl          p tc tvs ty) = return $ TypeDecl p tc tvs ty
  dictTrans (FunctionDecl p      pty f eqs) =
    FunctionDecl p (transformPredType pty) f <$> mapM dictTrans eqs
  dictTrans (PatternDecl           p t rhs) = case t of
    VariablePattern _ pty@(PredType ps _) v | not (Set.null ps) ->
      dictTrans $ FunctionDecl p pty v [Equation p (FunLhs NoSpanInfo v []) rhs]
    _ -> withLocalDictEnv $ PatternDecl p <$> dictTrans t <*> dictTrans rhs
  dictTrans d@(FreeDecl                _ _) = return $ fmap unpredType d
  dictTrans d@(ExternalDecl            _ _) = return $ fmap transformPredType d
  dictTrans d                               =
    internalError $ "Dictionary.dictTrans: " ++ show d

dictTransConstrDecl :: [Ident] -> ConstrDecl -> DataConstr -> ConstrDecl
dictTransConstrDecl tvs (ConstrDecl p c tes) dc =
  ConstrDecl p c $ map (fromType $ tvs ++ bvs) (constrTypes dc)
  where bvs = nub $ bv tes
dictTransConstrDecl tvs (ConOpDecl p ty1 op ty2) dc =
  dictTransConstrDecl tvs (ConstrDecl p op [ty1, ty2]) dc
dictTransConstrDecl _ d _ = internalError $ "Dictionary.dictTrans: " ++ show d

instance DictTrans Equation where
  dictTrans (Equation p (FunLhs _ f ts) rhs) =
    withLocalValueEnv $ withLocalDictEnv $ do
      m <- getModuleIdent
      pls <- matchPredList (varType m f) $
               foldr (TypeArrow . typeOf) (typeOf rhs) ts
      ts' <- addDictArgs pls ts
      modifyValueEnv $ bindPatterns ts'
      Equation p (FunLhs NoSpanInfo f ts') <$> dictTrans rhs
  dictTrans eq                               =
    internalError $ "Dictionary.dictTrans: " ++ show eq

instance DictTrans Rhs where
  dictTrans (SimpleRhs p _ e []) = simpleRhs p <$> dictTrans e
  dictTrans rhs                  =
    internalError $ "Dictionary.dictTrans: " ++ show rhs

instance DictTrans Pattern where
  dictTrans (LiteralPattern        _ pty l) =
    return $ LiteralPattern NoSpanInfo (unpredType pty) l
  dictTrans (VariablePattern       _ pty v) =
    return $ VariablePattern NoSpanInfo (unpredType pty) v
  dictTrans (ConstructorPattern _ pty c ts) = do
    pls <- matchPredList (conType c) $
             foldr (TypeArrow . typeOf) (unpredType pty) ts
    ConstructorPattern NoSpanInfo (unpredType pty) c <$> addDictArgs pls ts
  dictTrans (AsPattern               _ v t) =
    AsPattern NoSpanInfo v <$> dictTrans t
  dictTrans t                               =
    internalError $ "Dictionary.dictTrans: " ++ show t

instance DictTrans Expression where
  dictTrans (Literal     _ pty l) =
    return $ Literal NoSpanInfo (unpredType pty) l
  dictTrans (Variable    _ pty v) = do
    pls <- matchPredList (funType v) (unpredType pty)
    es <- mapM dictArg pls
    let ty = foldr (TypeArrow . typeOf) (unpredType pty) es
    return $ apply (Variable NoSpanInfo ty v) es
  dictTrans (Constructor _ pty c) = do
    pls <- matchPredList (conType c) (unpredType pty)
    es <- mapM dictArg pls
    let ty = foldr (TypeArrow . typeOf) (unpredType pty) es
    return $ apply (Constructor NoSpanInfo ty c) es
  dictTrans (Apply       _ e1 e2) =
    Apply NoSpanInfo <$> dictTrans e1 <*> dictTrans e2
  dictTrans (Typed       _ e qty) =
    Typed NoSpanInfo <$> dictTrans e <*> dictTransQualTypeExpr qty
  dictTrans (Lambda       _ ts e) = withLocalValueEnv $ withLocalDictEnv $ do
    ts' <- mapM dictTrans ts
    modifyValueEnv $ bindPatterns ts'
    mkLambda ts' <$> dictTrans e
  dictTrans (Let        _ _ ds e) = withLocalValueEnv $ do
    modifyValueEnv $ bindDecls ds
    mkLet <$> mapM dictTrans ds <*> dictTrans e
  dictTrans (Case    _ _ ct e as) =
    mkCase ct <$> dictTrans e <*> mapM dictTrans as
  dictTrans e                   =
    internalError $ "Dictionary.dictTrans: " ++ show e

-- Just like before in desugaring, we ignore the context in the type signature
-- of a typed expression, since there should be no possibility to provide a
-- non-empty context without scoped type-variables.
-- TODO: Verify

dictTransQualTypeExpr :: QualTypeExpr -> DTM QualTypeExpr
dictTransQualTypeExpr (QualTypeExpr spi _ ty) = return $ QualTypeExpr spi [] ty

instance DictTrans Alt where
  dictTrans (Alt p t rhs) = withLocalValueEnv $ withLocalDictEnv $ do
    t' <- dictTrans t
    modifyValueEnv $ bindPattern t'
    Alt p t' <$> dictTrans rhs

addDictArgs :: [Pred] -> [Pattern PredType] -> DTM [Pattern Type]
addDictArgs pls ts = do
  dictVars <- mapM (freshVar "_#dict" . rtDictType) pls
  clsEnv <- getClassEnv
  modifyDictEnv $ (++) $ dicts clsEnv $ zip pls (map (uncurry mkVar) dictVars)
  (++) (map (uncurry (VariablePattern NoSpanInfo )) dictVars)
         <$> mapM dictTrans ts
  where dicts clsEnv vs
          | null vs = vs
          | otherwise = vs ++ dicts clsEnv (concatMap (superDicts clsEnv) vs)
        superDicts clsEnv (Pred _ cls tys, e) =
          map (superDict cls tys e) $ Set.toList $ superClasses cls clsEnv
        superDict cls tys e sclsPred =
          ( expandAliasType tys sclsPred
          , Apply NoSpanInfo (superDictExpr cls sclsPred tys) e )
        superDictExpr cls sclsPred tys =
          Variable NoSpanInfo (superDictStubType cls sclsPred tys)
            (qSuperDictStubId cls sclsPred)

-- The function 'dictArg' constructs the dictionary argument for a predicate
-- from the predicates of a class method or an overloaded function. It checks
-- whether a dictionary for the predicate is available in the dictionary
-- environment, which is the case when the predicate is mentioned in the type
-- signature or is not reducible, and uses 'instDict' otherwise in order to
-- supply a new dictionary using the appropriate instance dictionary
-- construction function. If the corresponding instance declaration has a
-- non-empty context, the dictionary construction function is applied to the
-- dictionaries computed for the context instantiated at the appropriate types.

-- TODO: With FlexibleInstances, there could exist instances even for predicates
--         with only variable types. The comment above has to be updated for
--         that (as well as possibly the implementation below).

dictArg :: Pred -> DTM (Expression Type)
dictArg p = maybeM (instDict p) return (lookup p <$> getDictEnv)

instDict :: Pred -> DTM (Expression Type)
instDict p = instPredList p >>= flip (uncurry3 instFunApp) p

instFunApp :: ModuleIdent -> [Type] -> [Pred] -> Pred -> DTM (Expression Type)
instFunApp m tys pls p@(Pred _ cls _) = apply (Variable NoSpanInfo ty' f)
  <$> mapM dictArg pls
  where f   = qInstFunId m cls tys
        ty' = foldr1 TypeArrow $ map rtDictType $ pls ++ [p]

instPredList :: Pred -> DTM (ModuleIdent, [Type], [Pred])
instPredList (Pred _ cls tys) = do
  inEnv <- getInstEnv
  case fst (lookupInstMatch cls tys inEnv) of
    [] -> internalError $ "Dictionary.instPredList: " ++
                            "Could not find an instance for " ++ show (cls, tys)
    [(m, ps, itys, _, tau)] -> return (m, itys, subst tau (Set.toAscList ps))
    _ : _ : _ -> internalError $ "Dictionary.instPredList: " ++
                                   "Multiple instances for " ++ show (cls, tys)

-- When adding dictionary arguments on the left hand side of an equation and
-- in applications, respectively, the compiler must unify the function's type
-- with the concrete instance at which that type is used in order to determine
-- the correct context.

-- Polymorphic methods make things a little bit more complicated. When an
-- instance dictionary constructor is applied to an instance method, the
-- suffix of the instance method type's context that corresponds to the
-- additional constraints of the type class method must be discarded and
-- no dictionaries must be added for these constraints. Unfortunately, the
-- dictionary transformation has already been applied to the component types
-- of the dictionary constructor. Therefore, the function 'matchPredList'
-- tries to find a suffix of the context whose transformation matches the
-- initial arrows of the instance type.

matchPredList :: (ValueEnv -> TypeScheme) -> Type -> DTM [Pred]
matchPredList tySc ty2 = do
  ForAll _ (PredType ps ty1) <- tySc <$> getValueEnv
  return $ foldr (\(pls1, pls2) pls' ->
                   fromMaybe pls' $ qualMatch pls1 ty1 pls2 ty2)
                 (internalError $ "Dictionary.matchPredList: " ++ show ps)
                 (splits $ removeICCFlagList $ Set.toAscList ps)
 where
  -- Converts any implicit class constraint to a regular predicate so that given
  -- predicates from the dictionary environment can be easily assigned to
  -- required predicates.
  removeICCFlagList :: [Pred] -> [Pred]
  removeICCFlagList (Pred ICC qcls tys : pls) = Pred OPred qcls tys : pls
  removeICCFlagList pls                       = pls

qualMatch :: [Pred] -> Type -> [Pred] -> Type -> Maybe [Pred]
qualMatch pls1 ty1 pls2 ty2 = case predListMatch pls2 ty2 of
  Just ty2' -> Just $ subst (matchType ty1 ty2' idSubst) pls1
  Nothing -> Nothing

predListMatch :: [Pred] -> Type -> Maybe Type
predListMatch []     ty = Just ty
predListMatch (p:ps) ty = case ty of
  TypeForall _ ty'                                 -> predListMatch (p : ps) ty'
  TypeArrow ty1 ty2 | ty1 == rtDictType (instPred p) -> predListMatch ps ty2
  _                                                -> Nothing

splits :: [a] -> [([a], [a])]
splits xs = zip (inits xs) (tails xs)

-- -----------------------------------------------------------------------------
-- Optimizing method calls
-- -----------------------------------------------------------------------------

-- Whenever a type class method is applied to known types only, the compiler can
-- apply the type instance's implementation directly.

type SpecEnv = Map.Map (QualIdent, QualIdent) QualIdent

emptySpEnv :: SpecEnv
emptySpEnv = Map.empty

initSpEnv :: ClassEnv -> InstEnv -> SpecEnv
initSpEnv clsEnv = foldr (uncurry bindInstance) emptySpEnv . instEnvList
  where bindInstance (cls, tys) (m, _, _) =
          flip (foldr $ bindInstanceMethod m cls tys) $ classMethods cls clsEnv
        bindInstanceMethod m cls tys f = Map.insert (f', d) f''
          where f'  = qualifyLike cls f
                d   = qInstFunId m cls tys
                f'' = qImplMethodId m cls tys f

class Specialize a where
  specialize :: a Type -> DTM (a Type)

instance Specialize Module where
  specialize (Module spi li ps m es is ds) = do
    clsEnv <- getClassEnv
    inEnv <- getInstEnv
    setSpEnv $ initSpEnv clsEnv inEnv
    Module spi li ps m es is <$> mapM specialize ds

instance Specialize Decl where
  specialize (FunctionDecl p ty f eqs) =
    FunctionDecl p ty f <$> mapM specialize eqs
  specialize (PatternDecl     p t rhs) = PatternDecl p t <$> specialize rhs
  specialize d                         = return d

instance Specialize Equation where
  specialize (Equation p lhs rhs) = Equation p lhs <$> specialize rhs

instance Specialize Rhs where
  specialize (SimpleRhs p _ e []) = simpleRhs p <$> specialize e
  specialize rhs                  =
    internalError $ "Dictionary.specialize: " ++ show rhs

instance Specialize Expression where
  specialize e = specialize' e []

specialize' :: Expression Type -> [Expression Type] -> DTM (Expression Type)
specialize' l@(Literal     _ _ _) es = return $ apply l es
specialize' v@(Variable   _ _ v') es = do
  spEnv <- getSpEnv
  return $ case Map.lookup (v', f) spEnv of
    Just f' -> apply (Variable NoSpanInfo ty' f') $ es'' ++ es'
    Nothing -> apply v es
  where d:es' = es
        (Variable _ _ f, es'') = unapply d []
        ty' = foldr (TypeArrow . typeOf) (typeOf $ Apply NoSpanInfo v d) es''
specialize' c@(Constructor _ _ _) es = return $ apply c es
specialize' (Typed       _ e qty) es = do
  e' <- specialize e
  return $ apply (Typed NoSpanInfo e' qty) es
specialize' (Apply       _ e1 e2) es = do
  e2' <- specialize e2
  specialize' e1 $ e2' : es
specialize' (Lambda       _ ts e) es = do
  e' <- specialize e
  return $ apply (Lambda NoSpanInfo ts e') es
specialize' (Let        _ _ ds e) es = do
  ds' <- mapM specialize ds
  e' <- specialize e
  return $ apply (mkLet ds' e') es
specialize' (Case    _ _ ct e as) es = do
  e' <- specialize e
  as' <- mapM specialize as
  return $ apply (mkCase ct e' as') es
specialize' e                   _  =
  internalError $ "Dictionary.specialize': " ++ show e

instance Specialize Alt where
  specialize (Alt p t rhs) = Alt p t <$> specialize rhs

-- -----------------------------------------------------------------------------
-- Cleaning up
-- -----------------------------------------------------------------------------

-- After we have transformed the module we have to remove class exports from
-- the export list and type classes from the type constructor environment.
-- Furthermore, we may have to remove some infix declarations and operators
-- from the precedence environment as functions with class constraints have
-- been supplemented with additional dictionary arguments during the dictionary
-- transformation.

cleanup :: Module a -> DTM (Module a)
cleanup (Module spi li ps m es is ds) = do
  cleanedEs <- traverse cleanupExportSpec es
  cleanedDs <- concatMapM cleanupInfixDecl ds
  cleanupTyConsEnv
  cleanupPrecEnv
  return $ Module spi li ps m cleanedEs is cleanedDs

cleanupExportSpec :: ExportSpec -> DTM ExportSpec
cleanupExportSpec (Exporting p es) = Exporting p <$> concatMapM cleanupExport es

cleanupExport :: Export -> DTM [Export]
cleanupExport e@(Export             _ _) = return [e]
cleanupExport e@(ExportTypeWith spi tc cs) = do
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo tc tcEnv of
    [TypeClass _ _ _] -> return $ map (Export spi . qualifyLike tc) cs
    _                 -> return [e]
cleanupExport e                        =
  internalError $ "Dictionary.cleanupExport: " ++ show e

cleanupInfixDecl :: Decl a -> DTM [Decl a]
cleanupInfixDecl (InfixDecl p fix pr ops) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  let opArity = arrowArity . rawType . flip opType vEnv . qualifyWith m
      ops' = filter ((== 2) . opArity) ops
  return [InfixDecl p fix pr ops' | not (null ops')]
cleanupInfixDecl d                        = return [d]

cleanupTyConsEnv :: DTM ()
cleanupTyConsEnv = getTyConsEnv >>= mapM_ (cleanupTyCons . fst) . allBindings

cleanupTyCons :: QualIdent -> DTM ()
cleanupTyCons tc = do
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo tc tcEnv of
    [TypeClass _ _ _] -> modifyTyConsEnv $ qualUnbindTopEnv tc
    _                 -> return ()

cleanupPrecEnv :: DTM ()
cleanupPrecEnv = getPrecEnv >>= mapM_ (cleanupOp . fst) . allBindings

cleanupOp :: QualIdent -> DTM ()
cleanupOp op = do
  opArity <- arrowArity . rawType . opType op <$> getValueEnv
  when (opArity /= 2) $ modifyPrecEnv $ qualUnbindTopEnv op

-- -----------------------------------------------------------------------------
-- Transforming interfaces
-- -----------------------------------------------------------------------------

-- The following functions expect an already transformed value environment.
-- The transformation of interface declarations with it is quite simple and
-- straightforward.

dictTransInterfaces :: ValueEnv -> ClassEnv -> InterfaceEnv -> InterfaceEnv
dictTransInterfaces vEnv clsEnv = fmap $ dictTransInterface vEnv clsEnv

dictTransInterface :: ValueEnv -> ClassEnv -> Interface -> Interface
dictTransInterface vEnv clsEnv (Interface m is ds) =
  Interface m is $ concatMap (dictTransIDecl m vEnv clsEnv) ds

dictTransIDecl :: ModuleIdent -> ValueEnv -> ClassEnv -> IDecl -> [IDecl]
dictTransIDecl m vEnv _      d@(IInfixDecl         _ _ _ op)
  | arrowArity (rawType $ opType (qualQualify m op) vEnv) /= 2 = []
  | otherwise = [d]
dictTransIDecl _ _    _      d@(HidingDataDecl      _ _ _ _) = [d]
dictTransIDecl m _    _      (IDataDecl    p tc k tvs cs hs) =
  [IDataDecl p tc k tvs (map (dictTransIConstrDecl m tvs) cs) hs]
dictTransIDecl _ _    _      d@(INewtypeDecl    _ _ _ _ _ _) = [d]
dictTransIDecl _ _    _      d@(ITypeDecl         _ _ _ _ _) = [d]
dictTransIDecl m vEnv _      (IFunctionDecl       _ f _ _ _) =
  [iFunctionDeclFromValue m vEnv (qualQualify m f)]
dictTransIDecl _ _    _      (HidingClassDecl p _ cls k tvs) =
  [HidingDataDecl p (qDictTypeId cls) k' tvs]
  where k' = fmap (fromKind . dictTypeKind cls . toKind) k
dictTransIDecl m vEnv clsEnv (IClassDecl p _ cls k tvs _ hs) =
  dictDecl : defaults ++ methodStubs ++ superDictStubs
 where
  qcls        = qualQualify m cls
  ms          = classMethods qcls clsEnv
  k'          = fmap (fromKind . dictTypeKind cls . toKind) k
  sclss       = Set.toAscList (superClasses qcls clsEnv)
  dictDecl    = IDataDecl p (qDictTypeId cls) k'
                  (take (length tvs) identSupply) [constrDecl] []
  constrDecl  = iConstrDeclFromDataConstructor m vEnv $ qDictConstrId qcls
  defaults    = map (iFunctionDeclFromValue m vEnv . qDefaultMethodId qcls) ms
  methodStubs = map (iFunctionDeclFromValue m vEnv . qualifyLike qcls) $
                  filter (`notElem` hs) ms
  superDictStubs = map (iFunctionDeclFromValue m vEnv . qSuperDictStubId qcls)
                     sclss
dictTransIDecl m vEnv clsEnv (IInstanceDecl _ _ cls tys _ mm) =
  iFunctionDeclFromValue m vEnv (qInstFunId m' qcls tys') :
    map (iFunctionDeclFromValue m vEnv . qImplMethodId m' qcls tys') ms
  where m'   = fromMaybe m mm
        qcls = qualQualify m cls
        tys' = toQualTypes m [] tys
        ms   = classMethods qcls clsEnv

dictTransIConstrDecl :: ModuleIdent -> [Ident] -> ConstrDecl -> ConstrDecl
dictTransIConstrDecl _ _ (ConOpDecl p ty1 op ty2) = ConstrDecl p op [ty1, ty2]
dictTransIConstrDecl _ _ cd                       = cd

iFunctionDeclFromValue :: ModuleIdent -> ValueEnv -> QualIdent -> IDecl
iFunctionDeclFromValue m vEnv f = case qualLookupValue f vEnv of
  [Value _ _ a (ForAll _ pty)] ->
    IFunctionDecl NoPos (qualUnqualify m f) Nothing a $
      fromQualPredType m identSupply pty
  _ -> internalError $ "Dictionary.iFunctionDeclFromValue: " ++ show f

iConstrDeclFromDataConstructor :: ModuleIdent -> ValueEnv -> QualIdent
                               -> ConstrDecl
iConstrDeclFromDataConstructor m vEnv c = case qualLookupValue c vEnv of
  [DataConstructor _ _ _ (ForAll _ pty)] ->
    ConstrDecl NoSpanInfo (unqualify c) tys
    where tys = map (fromQualType m identSupply) $ arrowArgs $ unpredType pty
  _ -> internalError $ "Dictionary.iConstrDeclFromDataConstructor: " ++ show c

-- -----------------------------------------------------------------------------
-- Functions for naming newly created types, functions and parameters
-- -----------------------------------------------------------------------------

-- The following functions provide normalized identifiers for dictionary data
-- types, dictionary data constructors, default method implementations, super
-- class dictionary stub functions, instance dictionary functions and instance
-- method implementations. All identifiers are available both qualified and
-- unqualified.
--
-- In these identifiers, type variables are displayed as numbers to avoid name
-- clashes with type constructors and type arguments (needed for super class
-- relations and instance types) are always parenthesized to circumvent the need
-- for other separators. With the exception of the dictionary data type and
-- constructor identifiers, all classes and data types are represented by their
-- original names, which are always unique.
--
-- For some examples of these identifiers, we consider a class with the
-- qualified name M.C and a class method cf. For these, we get:
--
-- Dictionary data type and constructor:  _Dict#C
-- Default method implementation:         _def#cf#M.C
--
-- Super class dictionary stubs consist of the name of the subclass, the super
-- class name and information about the type variables that the super class is
-- applied to in the class definition. More concretely, for each super class
-- type argument, the index of the respective subclass variable is added to the
-- identifier in parentheses. As an example, we consider the super class
-- relation shown in the class declaration class N.D b b a => C a b c
--
-- Super class dictionary stub:  _super#M.C#N.D(1)(1)(0)
--
-- Instance dictionary functions consist of the full instance head, where all
-- type constructors, including the class, are displayed with their name, type
-- variables are displayed as with their indices, and type arguments are
-- parenthesized each. Instance method implementations are identified like the
-- dictionary functions, but with the method name added before the class name.
-- For both kinds of functions, it is important that their identifiers are
-- generated using the instance types from the instance environment.
-- Examples are shown for the instance declaration instance M.C Int [a] (b, a):
--
-- Instance dictionary function:    _inst#M.C(Prelude.Int)([](0))((,)(1)(0))
-- Instance method implementation:  _impl#cf#M.C(Prelude.Int)([](0))((,)(1)(0))

dictTypeId :: QualIdent -> Ident
dictTypeId cls = mkIdent $ "_Dict#" ++ idName (unqualify cls)

qDictTypeId :: QualIdent -> QualIdent
qDictTypeId cls = qualifyLike cls $ dictTypeId cls

dictConstrId :: QualIdent -> Ident
dictConstrId = dictTypeId

qDictConstrId :: QualIdent -> QualIdent
qDictConstrId cls = qualifyLike cls $ dictConstrId cls

defaultMethodId :: QualIdent -> Ident -> Ident
defaultMethodId cls f = mkIdent $ "_def#" ++ idName f ++ '#' : qualName cls

qDefaultMethodId :: QualIdent -> Ident -> QualIdent
qDefaultMethodId cls = qualifyLike cls . defaultMethodId cls

superDictStubId :: QualIdent -> Pred -> Ident
superDictStubId cls (Pred _ scls tys) = mkIdent $ "_super#" ++ qualName cls ++
  '#' : qualName scls ++ concatMap typeId tys

qSuperDictStubId :: QualIdent -> Pred -> QualIdent
qSuperDictStubId cls = qualifyLike cls . superDictStubId cls

instFunId :: QualIdent -> [Type] -> Ident
instFunId cls tys = mkIdent $
  "_inst#" ++ qualName cls ++ concatMap typeId tys

qInstFunId :: ModuleIdent -> QualIdent -> [Type] -> QualIdent
qInstFunId m cls = qualifyWith m . instFunId cls

implMethodId :: QualIdent -> [Type] -> Ident -> Ident
implMethodId cls tys f = mkIdent $
  "_impl#" ++ idName f ++ '#' : qualName cls ++ concatMap typeId tys

qImplMethodId :: ModuleIdent -> QualIdent -> [Type] -> Ident -> QualIdent
qImplMethodId m cls tys = qualifyWith m . implMethodId cls tys

typeId :: Type -> String
typeId ty = '(' : typeId' ty ++ ")"
 where
  typeId' (TypeConstructor  tc) = qualName tc
  typeId' (TypeVariable      v) = show v
  typeId' (TypeApply   ty1 ty2) = typeId' ty1 ++ typeId ty2
  typeId' (TypeArrow   ty1 ty2) = qualName qArrowId ++ typeId ty1 ++ typeId ty2
  typeId' (TypeForall    _ ty') = typeId' ty'
  typeId' (TypeConstrained _ _) = internalError "Dictionary.typeId"

-- -----------------------------------------------------------------------------
-- Generating variables
-- -----------------------------------------------------------------------------

freshVar :: String -> Type -> DTM (Type, Ident)
freshVar name ty = ((,) ty) . mkIdent . (name ++) . show <$> getNextId

-- -----------------------------------------------------------------------------
-- Auxiliary functions
-- -----------------------------------------------------------------------------

-- The function 'dictType' returns the type of the dictionary corresponding to
-- a particular C-T instance.

rtDictType :: Pred -> Type
rtDictType = TypeArrow unitType . dictType

dictType :: Pred -> Type
dictType (Pred _ cls tys) = applyType (TypeConstructor $ qDictTypeId cls) tys

-- Converts the kind of a type class to the kind of the respective dictionary
-- type by changing the Constraint at the end of the class kind to a *.
dictTypeKind :: QualIdent -> Kind -> Kind
dictTypeKind cls k = dictTypeKind' k
 where
  dictTypeKind' :: Kind -> Kind
  dictTypeKind' KindConstraint    = KindStar
  dictTypeKind' (KindArrow k1 k2) = KindArrow k1 (dictTypeKind' k2)
  dictTypeKind' _ = internalError $ "Dictionary.dictTypeKind: Class " ++
                                      show cls ++ " has invalid kind " ++ show k

-- The function 'transformPredType' replaces each predicate with a new
-- dictionary type argument.

transformPredType :: PredType -> Type
transformPredType (PredType ps ty) =
  foldr (TypeArrow . rtDictType) ty $ Set.toList ps

-- The function 'transformMethodPredType' first deletes the implicit class
-- constraint and then transforms the resulting predicated type as above.
-- Additionally, it returns the arity of the class in this constraint.

transformMethodPredType :: PredType -> (Type, Int)
transformMethodPredType (PredType ps ty) =
  let iccAr = maybe 0 (\(Pred _ _ tys) -> length tys) (Set.lookupMin ps)
  in (transformPredType $ PredType (Set.deleteMin ps) ty, iccAr)

-- The function 'generalizeMethodType' generalizes an already transformed
-- method type to a forall type by quantifying all occurring type variables
-- except for the class variables whose indices are between 0 (inclusive) and
-- the given class arity (exclusive). This function is uncurried by default so
-- it can more easily be combined with 'transformMethodPredType'.
-- TODO: Check if the < 0 test can be removed.
generalizeMethodType :: (Type, Int) -> Type
generalizeMethodType (ty, clsAr)
  | null tvs  = ty
  | otherwise = TypeForall tvs ty
  where tvs = nub $ filter (\i -> i >= clsAr || i < 0) $ typeVars ty

instTypeVar :: Int -> Int
instTypeVar tv = -1 - tv

instType :: Type -> Type
instType (TypeConstructor tc) = TypeConstructor tc
instType (TypeVariable    tv) = TypeVariable (instTypeVar tv)
instType (TypeApply  ty1 ty2) = TypeApply (instType ty1) (instType ty2)
instType (TypeArrow  ty1 ty2) = TypeArrow (instType ty1) (instType ty2)
instType (TypeForall  tvs ty) = TypeForall (map instTypeVar tvs) (instType ty)
instType ty = ty

instPred :: Pred -> Pred
instPred (Pred isIcc cls ty) = Pred isIcc cls (map instType ty)

unRenameIdentIf :: Bool -> Ident -> Ident
unRenameIdentIf b = if b then unRenameIdent else id

-- The string for the error message for a class method's default method
-- implementation has to be constructed in its desugared form since the
-- desugaring has already taken place.

preludeError :: Type -> String -> Expression PredType
preludeError a =
  Apply NoSpanInfo (Variable NoSpanInfo
                     (predType (TypeArrow stringType a)) qErrorId) . stringExpr

stringExpr :: String -> Expression PredType
stringExpr = foldr (consExpr . Literal NoSpanInfo (predType charType) . Char)
               nilExpr
  where
  nilExpr = Constructor NoSpanInfo (predType stringType) qNilId
  consExpr = (Apply NoSpanInfo) . (Apply NoSpanInfo)
    (Constructor NoSpanInfo (predType $ consType charType) qConsId)

-- The function 'varType' is able to lookup both local and global identifiers.
-- Since the environments have been qualified before, global declarations are
-- only visible under their original name whereas local declarations are always
-- entered unqualified. 'varType' transforms the implicit class constraint of
-- the requested variable, if it has any, to a regular predicate. This is
-- necessary because 'varType' is used in the module transformation to retrieve
-- the types of functions with implicit class constraints like default method
-- implementations.

-- The function 'funType' has a boolean parameter which marks whether the
-- implicit class constraint of the requested function, if it has any, should be
-- transformed into a regular predicate. This functionality should be used when
-- using this type information to check the types of expressions that could
-- contain class methods (here, this is the case for the module transformation).
-- It should only be disabled if the implicit class constraint of a requested 
-- class method has to be treated differently than other predicates.

varType :: ModuleIdent -> Ident -> ValueEnv -> TypeScheme
varType m v vEnv = case qualLookupValue (qualify v) vEnv of
  Value _ _ _ tySc : _ -> tySc
  Label _ _   tySc : _ -> tySc
  _ -> case qualLookupValue (qualifyWith m v) vEnv of
    Value _ _ _ tySc : _ -> tySc
    Label _ _   tySc : _ -> tySc
    _ -> internalError $ "Dictionary.varType: " ++ show v

conType :: QualIdent -> ValueEnv -> TypeScheme
conType c vEnv = case qualLookupValue c vEnv of
  [DataConstructor  _ _ _ (ForAll n pty)] -> ForAll n pty
  [NewtypeConstructor _ _ (ForAll n pty)] -> ForAll n pty
  _ -> internalError $ "Dictionary.conType: " ++ show c

funType :: QualIdent -> ValueEnv -> TypeScheme
funType f vEnv = case qualLookupValue f vEnv of
  [Value _ _ _ tySc] -> tySc
  [Label _ _   tySc] -> tySc
  _ -> internalError $ "Dictionary.funType " ++ show f

opType :: QualIdent -> ValueEnv -> TypeScheme
opType op vEnv = case qualLookupValue op vEnv of
  [DataConstructor  _ _ _ (ForAll n pty)] -> ForAll n pty
  [NewtypeConstructor _ _ (ForAll n pty)] -> ForAll n pty
  [Value _ _ _                      tySc] -> tySc
  [Label _ _                        tySc] -> tySc
  _ -> internalError $ "Dictionary.opType " ++ show op
