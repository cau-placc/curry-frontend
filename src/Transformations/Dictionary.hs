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
import qualified Data.Map   as Map ( Map, empty, insert, lookup, mapWithKey
                                   , toList )
import           Data.Maybe        (fromMaybe, isJust)
import qualified Data.Set   as Set ( deleteMin, fromList, null, size, toAscList
                                   , toList, union )

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.CurryTypes
import Base.Expr
import Base.Kinds
import Base.Messages (internalError)
import Base.TopEnv
import Base.Types
import Base.TypeSubst
import Base.Typing

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
  , augmentEnv  :: AugmentEnv -- for augmenting nullary class methods
  , dictEnv     :: DictEnv    -- for dictionary insertion
  , specEnv     :: SpecEnv    -- for dictionary specialization
  , nextId      :: Integer
  }

type DTM = S.State DTState

insertDicts :: InterfaceEnv -> TCEnv -> ValueEnv -> ClassEnv -> InstEnv
            -> OpPrecEnv -> Module PredType
            -> (Module Type, InterfaceEnv, TCEnv, ValueEnv, OpPrecEnv)
insertDicts intfEnv tcEnv vEnv clsEnv inEnv pEnv mdl@(Module _ m _ _ _) =
  (mdl', intfEnv', tcEnv', vEnv', pEnv')
  where initState =
          DTState m tcEnv vEnv clsEnv inEnv pEnv emptyAugEnv emptyDictEnv emptySpEnv 1
        (mdl', tcEnv', vEnv', pEnv') =
          runDTM (augment mdl >>= dictTrans >>= specialize >>= cleanup) initState
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

getAugEnv :: DTM AugmentEnv
getAugEnv = S.gets augmentEnv

setAugEnv :: AugmentEnv -> DTM ()
setAugEnv augEnv = S.modify $ \s -> s { augmentEnv = augEnv }

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
-- Augmenting nullary class methods
-- -----------------------------------------------------------------------------

-- To prevent unwanted sharing of non-determinism for nullary class methods
-- we augment them with an additional unit argument.

type AugmentEnv = [QualIdent]

emptyAugEnv :: AugmentEnv
emptyAugEnv = []

initAugEnv :: ValueEnv -> AugmentEnv
initAugEnv = foldr (bindValue . snd) emptyAugEnv . allBindings
  where bindValue (Value f True _ (ForAll _ (PredType _ ty)))
          | arrowArity ty == 0 = (f :)
        bindValue _ = id

isAugmented :: AugmentEnv -> QualIdent -> Bool
isAugmented = flip elem

augmentValues :: ValueEnv -> ValueEnv
augmentValues = fmap augmentValueInfo

augmentValueInfo :: ValueInfo -> ValueInfo
augmentValueInfo (Value f True a (ForAll n (PredType ps ty)))
  | arrowArity ty == 0 = Value f True a $ ForAll n $ PredType ps ty'
  where ty' = augmentType ty
augmentValueInfo vi = vi

augmentTypes :: TCEnv -> TCEnv
augmentTypes = fmap augmentTypeInfo

augmentTypeInfo :: TypeInfo -> TypeInfo
augmentTypeInfo (TypeClass cls k ms) =
  TypeClass cls k $ map augmentClassMethod ms
augmentTypeInfo ti = ti

augmentClassMethod :: ClassMethod -> ClassMethod
augmentClassMethod mthd@(ClassMethod f a (PredType ps ty))
  | arrowArity ty == 0 =
    ClassMethod f (Just $ fromMaybe 0 a + 1) $ PredType ps $ augmentType ty
  | otherwise = mthd

augmentInstances :: AugmentEnv -> InstEnv -> InstEnv
augmentInstances = Map.mapWithKey . augmentInstInfo

augmentInstInfo :: AugmentEnv -> InstIdent -> InstInfo -> InstInfo
augmentInstInfo augEnv (cls, _) (m, ps, is) =
  (m, ps, map (augmentInstImpl augEnv cls) is)

augmentInstImpl :: AugmentEnv -> QualIdent -> (Ident, Int) -> (Ident, Int)
augmentInstImpl augEnv cls (f, a)
  | isAugmented augEnv (qualifyLike cls f) = (f, a + 1)
  | otherwise = (f, a)

class Augment a where
  augment :: a PredType -> DTM (a PredType)

instance Augment Module where
  augment (Module ps m es is ds) = do
    augEnv <- initAugEnv <$> getValueEnv
    setAugEnv augEnv
    modifyValueEnv $ augmentValues
    modifyTyConsEnv $ augmentTypes
    modifyInstEnv $ augmentInstances augEnv
    Module ps m es is <$> mapM (augmentDecl Nothing) ds

-- The first parameter of the functions 'augmentDecl', 'augmentEquation' and
-- 'augmentLhs' determines whether we have to unrename the function identifiers
-- before checking if the function has to augmented or not. Furthermore, it
-- specifies the module unqualified identifiers have to be qualified with.
-- The unrenaming is necessary for both class and instance declarations as all
-- identifiers within these have been renamed during the syntax check, while the
-- qualifying is needed for function declarations within instance declarations
-- as the implemented class methods can originate from another module. If not
-- qualified properly, the lookup in the augmentation environment would fail.

-- Since type signatures remain only in class declarations due to desugaring,
-- we can always perform the unrenaming and it is safe to assume that all other
-- functions mentioned in a type signature have to be augmented as well if the
-- first one is affected.

augmentDecl :: Maybe ModuleIdent -> Decl PredType -> DTM (Decl PredType)
augmentDecl _  d@(TypeSig          p fs qty) = do
  m <- getModuleIdent
  augEnv <- getAugEnv
  return $ if isAugmented augEnv (qualifyWith m $ unRenameIdent $ head fs)
              then TypeSig p fs $ augmentQualTypeExpr qty
              else d
augmentDecl mm (FunctionDecl    p pty f eqs) = do
    eqs' <- mapM (augmentEquation mm) eqs
    m <- maybe getModuleIdent return mm
    augEnv <- getAugEnv
    if isAugmented augEnv (qualifyWith m $ unRenameIdentIf (isJust mm) f)
      then return $ FunctionDecl p (augmentPredType pty) f eqs'
      else return $ FunctionDecl p pty f eqs'
augmentDecl _  (PatternDecl         p t rhs) = PatternDecl p t <$> augment rhs
augmentDecl _  (ClassDecl    p cx cls tv ds) = do
  m <- getModuleIdent
  ClassDecl p cx cls tv <$> mapM (augmentDecl $ Just m) ds
augmentDecl _  (InstanceDecl p cx cls ty ds) =
  InstanceDecl p cx cls ty <$> mapM (augmentDecl $ qidModule cls) ds
augmentDecl _ d                             = return d

augmentEquation :: Maybe ModuleIdent -> Equation PredType
                -> DTM (Equation PredType)
augmentEquation mm (Equation p lhs rhs) =
  Equation p <$> augmentLhs mm lhs <*> augment rhs

augmentLhs :: Maybe ModuleIdent -> Lhs PredType -> DTM (Lhs PredType)
augmentLhs mm lhs@(FunLhs f ts) = do
    m <- maybe getModuleIdent return mm
    augEnv <- getAugEnv
    if isAugmented augEnv (qualifyWith m $ unRenameIdentIf (isJust mm) f)
      then return $ FunLhs f $ ConstructorPattern predUnitType qUnitId [] : ts
      else return lhs
augmentLhs _ lhs               =
  internalError $ "Dictionary.augmentLhs" ++ show lhs

instance Augment Rhs where
  augment (SimpleRhs p e []) = simpleRhs p <$> augment e
  augment rhs                =
    internalError $ "Dictionary.augment: " ++ show rhs

instance Augment Expression where
  augment l@(Literal     _ _) = return l
  augment v@(Variable pty v') = do
    augEnv <- getAugEnv
    return $ if isAugmented augEnv v'
               then apply (Variable (augmentPredType pty) v')
                      [Constructor predUnitType qUnitId]
               else v
  augment c@(Constructor _ _) = return c
  augment (Typed       e qty) = flip Typed qty <$> augment e
  augment (Apply       e1 e2) = Apply <$> augment e1 <*> augment e2
  augment (Lambda       ts e) = Lambda ts <$> augment e
  augment (Let          ds e) =
    Let <$> mapM (augmentDecl Nothing) ds <*> augment e
  augment (Case      ct e as) = Case ct <$> augment e <*> mapM augment as
  augment e                   = internalError $ "Dictionary.augment: " ++ show e

instance Augment Alt where
  augment (Alt p t rhs) = Alt p t <$> augment rhs

augmentPredType :: PredType -> PredType
augmentPredType (PredType ps ty) = PredType ps $ augmentType ty

augmentType :: Type -> Type
augmentType = TypeArrow unitType

augmentQualTypeExpr :: QualTypeExpr -> QualTypeExpr
augmentQualTypeExpr (QualTypeExpr cx ty) = QualTypeExpr cx $ augmentTypeExpr ty

augmentTypeExpr :: TypeExpr -> TypeExpr
augmentTypeExpr = ArrowType $ ConstructorType qUnitId

-- -----------------------------------------------------------------------------
-- Lifting class and instance declarations
-- -----------------------------------------------------------------------------

-- When we lift class and instance declarations, we can remove the optional
-- default declaration since it has already been considered during the type
-- check.

liftDecls :: Decl PredType -> DTM [Decl PredType]
liftDecls (DefaultDecl _ _) = return []
liftDecls (ClassDecl _ _ cls tv ds) = do
  m <- getModuleIdent
  liftClassDecls (qualifyWith m cls) tv ds
liftDecls (InstanceDecl _ cx cls ty ds) = do
  clsEnv <- getClassEnv
  let PredType ps ty' = toPredType [] $ QualTypeExpr cx ty
      ps' = minPredSet clsEnv ps
  liftInstanceDecls ps' cls ty' ds
liftDecls d = return [d]

liftClassDecls :: QualIdent -> Ident -> [Decl PredType] -> DTM [Decl PredType]
liftClassDecls cls tv ds = do
  dictDecl <- createClassDictDecl cls tv ods
  clsEnv <- getClassEnv
  let fs = classMethods cls clsEnv
  methodDecls <- mapM (createClassMethodDecl cls ms) fs
  return $ dictDecl : methodDecls
  where (vds, ods) = partition isValueDecl ds
        ms = methodMap vds

liftInstanceDecls :: PredSet -> QualIdent -> Type -> [Decl PredType]
                  -> DTM [Decl PredType]
liftInstanceDecls ps cls ty ds = do
  dictDecl <- createInstDictDecl ps cls ty
  clsEnv <- getClassEnv
  let fs = classMethods cls clsEnv
  methodDecls <- mapM (createInstMethodDecl ps cls ty ms) fs
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

createClassDictDecl :: QualIdent -> Ident -> [Decl a] -> DTM (Decl a)
createClassDictDecl cls tv ds = do
  c <- createClassDictConstrDecl cls tv ds
  return $ DataDecl NoPos (dictTypeId cls) [tv] [c] []

createClassDictConstrDecl :: QualIdent -> Ident -> [Decl a] -> DTM ConstrDecl
createClassDictConstrDecl cls tv ds = do
  clsEnv <- getClassEnv
  let sclss = superClasses cls clsEnv
      cx    = [Constraint scls (VariableType tv) | scls <- sclss]
      tvs   = tv : filter (unRenameIdent tv /=) identSupply
      mtys  = map (fromType tvs . generalizeMethodType . transformMethodPredType)
                [toMethodType cls tv qty | TypeSig _ fs qty <- ds, _ <- fs]
  return $ ConstrDecl NoPos [] cx (dictConstrId cls) mtys

classDictConstrPredType :: ValueEnv -> ClassEnv -> QualIdent -> PredType
classDictConstrPredType vEnv clsEnv cls = PredType ps $ foldr TypeArrow ty mtys
  where sclss = superClasses cls clsEnv
        ps    = Set.fromList [Pred scls (TypeVariable 0) | scls <- sclss]
        fs    = classMethods cls clsEnv
        mptys = map (classMethodType vEnv cls) fs
        ty    = dictType $ Pred cls $ TypeVariable 0
        mtys  = map (generalizeMethodType . transformMethodPredType) mptys

createInstDictDecl :: PredSet -> QualIdent -> Type -> DTM (Decl PredType)
createInstDictDecl ps cls ty = do
  pty <- PredType ps . arrowBase <$> getInstDictConstrType cls ty
  funDecl NoPos pty (instFunId cls ty) [] <$> createInstDictExpr cls ty

createInstDictExpr :: QualIdent -> Type -> DTM (Expression PredType)
createInstDictExpr cls ty = do
  ty' <- instType <$> getInstDictConstrType cls ty
  m <- getModuleIdent
  clsEnv <- getClassEnv
  let fs = map (qImplMethodId m cls ty) $ classMethods cls clsEnv
  return $ apply (Constructor (predType ty') (qDictConstrId cls))
             (zipWith (Variable . predType) (arrowArgs ty') fs)

getInstDictConstrType :: QualIdent -> Type -> DTM Type
getInstDictConstrType cls ty = do
  vEnv <- getValueEnv
  clsEnv <- getClassEnv
  return $ instanceType ty $ unpredType $ classDictConstrPredType vEnv clsEnv cls

createClassMethodDecl :: QualIdent -> MethodMap -> Ident -> DTM (Decl PredType)
createClassMethodDecl cls =
  createMethodDecl (defaultMethodId cls) (defaultClassMethodDecl cls)

defaultClassMethodDecl :: QualIdent -> Ident -> DTM (Decl PredType)
defaultClassMethodDecl cls f = do
  pty@(PredType _ ty) <- getClassMethodType cls f
  augEnv <- getAugEnv
  let pats = if isAugmented augEnv (qualifyLike cls f)
               then [ConstructorPattern predUnitType qUnitId []]
               else []
  return $ funDecl NoPos pty f pats $ preludeError (instType ty) $
    "No instance or default method for class operation " ++ escName f

getClassMethodType :: QualIdent -> Ident -> DTM PredType
getClassMethodType cls f = do
  vEnv <- getValueEnv
  return $ classMethodType vEnv cls f

classMethodType :: ValueEnv -> QualIdent -> Ident -> PredType
classMethodType vEnv cls f = pty
  where ForAll _ pty = funType (qualifyLike cls f) vEnv

createInstMethodDecl :: PredSet -> QualIdent -> Type -> MethodMap -> Ident
                     -> DTM (Decl PredType)
createInstMethodDecl ps cls ty =
  createMethodDecl (implMethodId cls ty) (defaultInstMethodDecl ps cls ty)

defaultInstMethodDecl :: PredSet -> QualIdent -> Type -> Ident
                      -> DTM (Decl PredType)
defaultInstMethodDecl ps cls ty f = do
  vEnv <- getValueEnv
  let pty@(PredType _ ty') = instMethodType vEnv ps cls ty f
  return $ funDecl NoPos pty f [] $
    Variable (predType $ instType ty') (qDefaultMethodId cls f)

-- Returns the type for a given instance's method of a given class. To this
-- end, the class method's type is stripped of its first predicate (which is
-- the implicit class constraint) and the class variable is replaced with the
-- instance's type. The remaining predicate set is then united with the
-- instance's predicate set.

instMethodType :: ValueEnv -> PredSet -> QualIdent -> Type -> Ident -> PredType
instMethodType vEnv ps cls ty f = PredType (ps `Set.union` ps'') ty''
  where PredType ps'  ty'  = classMethodType vEnv cls f
        PredType ps'' ty'' = instanceType ty $ PredType (Set.deleteMin ps') ty'

createMethodDecl :: (Ident -> Ident) -> (Ident -> DTM (Decl PredType))
                 -> MethodMap -> Ident -> DTM (Decl PredType)
createMethodDecl methodId defaultDecl ms f =
  liftM (renameDecl $ methodId f) $ maybe (defaultDecl f) return (lookup f ms)

-- We have to rename the left hand side of lifted function declarations
-- accordingly which is done by the function 'renameDecl'.

renameDecl :: Ident -> Decl a -> Decl a
renameDecl f (FunctionDecl p a _ eqs) = FunctionDecl p a f $ map renameEq eqs
  where renameEq (Equation p' lhs rhs) = Equation p' (renameLhs lhs) rhs
        renameLhs (FunLhs _ ts) = FunLhs f ts
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
createStubs (ClassDecl _ _ cls _ _) = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  clsEnv <- getClassEnv
  let ocls  = qualifyWith m cls
      sclss = superClasses ocls clsEnv
      fs    = classMethods ocls clsEnv
      dictConstrPty = classDictConstrPredType vEnv clsEnv ocls
      (superDictAndMethodTys, dictTy) =
        arrowUnapply $ transformPredType dictConstrPty
      (superDictTys, methodTys)       =
        splitAt (length sclss) superDictAndMethodTys
      (superStubTys, methodStubTys)   =
        splitAt (length sclss) $ map (TypeArrow dictTy) superDictAndMethodTys
  superDictVs <- mapM (freshVar "_#super" . instType) superDictTys
  methodVs <- mapM (freshVar "_#meth" . instType) methodTys
  methodDictTyss <- zipWithM (computeMethodDictTypes ocls) fs methodTys
  methodDictVss <- mapM (mapM $ freshVar "_#dict" . instType) methodDictTyss
  let patternVs   = superDictVs ++ methodVs
      pattern     = createDictPattern (instType dictTy) ocls patternVs
      superStubs  = zipWith3 (createSuperDictStubDecl pattern ocls)
                      superStubTys sclss superDictVs
      methodStubs = zipWith4 (createMethodStubDecl pattern)
                      methodStubTys fs methodVs methodDictVss
  return $ superStubs ++ methodStubs
createStubs _ = return []

-- Computes the additional dictionary arguments of a transformed method type
-- which correspond to the constraints of the original class method's type.

computeMethodDictTypes :: QualIdent -> Ident -> Type -> DTM [Type]
computeMethodDictTypes cls f ty = do
  PredType _ ty' <- getClassMethodType cls f
  return $ take (length tys - arrowArity ty') tys
  where tys = arrowArgs ty

createDictPattern :: a -> QualIdent -> [(a, Ident)] -> Pattern a
createDictPattern a cls = constrPattern a (qDictConstrId cls)

createSuperDictStubDecl :: Pattern a -> QualIdent -> a -> QualIdent
                        -> (a, Ident) -> Decl a
createSuperDictStubDecl t cls a super v =
  createStubDecl t a (superDictStubId cls super) v []

createMethodStubDecl :: Pattern a -> a -> Ident -> (a, Ident) -> [(a, Ident)]
                     -> Decl a
createMethodStubDecl = createStubDecl

createStubDecl :: Pattern a -> a -> Ident -> (a, Ident) -> [(a, Ident)]
               -> Decl a
createStubDecl t a f v us = FunctionDecl NoPos a f [createStubEquation t f v us]

createStubEquation :: Pattern a -> Ident -> (a, Ident) -> [(a, Ident)]
                   -> Equation a
createStubEquation t f v us =
  mkEquation NoPos f (t : map (uncurry VariablePattern) us) $
    apply (uncurry mkVar v) (map (uncurry mkVar) us)

superDictStubType :: QualIdent -> QualIdent -> Type -> Type
superDictStubType cls super ty =
  TypeArrow (dictType $ Pred cls ty) (dictType $ Pred super ty)

-- -----------------------------------------------------------------------------
-- Entering new bindings into the environments
-- -----------------------------------------------------------------------------

bindDictTypes :: ModuleIdent -> ClassEnv -> TCEnv -> TCEnv
bindDictTypes m clsEnv tcEnv =
  foldr (bindDictType m clsEnv) tcEnv (allEntities tcEnv)

bindDictType :: ModuleIdent -> ClassEnv -> TypeInfo -> TCEnv -> TCEnv
bindDictType m clsEnv (TypeClass cls k ms) = bindEntity m tc ti
  where ti    = DataType tc (KindArrow k KindStar) [c]
        tc    = qDictTypeId cls
        c     = DataConstr (dictConstrId cls) 0 ps tys
        sclss = superClasses cls clsEnv
        ps    = Set.fromList [Pred scls (TypeVariable 0) | scls <- sclss]
        tys   = map (generalizeMethodType . transformMethodPredType . methodType) ms
bindDictType _ _      _                    = id

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
  bindClassDict m clsEnv cls . bindSuperStubs m cls sclss .
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
        tySc = ForAllExist 1 0 pty

bindDefaultMethods :: ModuleIdent -> QualIdent -> [(Ident, Int)] -> ValueEnv
                   -> ValueEnv
bindDefaultMethods m = flip . foldr . bindDefaultMethod m

bindDefaultMethod :: ModuleIdent -> QualIdent -> (Ident, Int) -> ValueEnv
                  -> ValueEnv
bindDefaultMethod m cls (f, n) vEnv =
  bindMethod m (qDefaultMethodId cls f) n (classMethodType vEnv cls f) vEnv

bindSuperStubs :: ModuleIdent -> QualIdent -> [QualIdent] -> ValueEnv
               -> ValueEnv
bindSuperStubs m = flip . foldr . bindSuperStub m

bindSuperStub :: ModuleIdent -> QualIdent -> QualIdent -> ValueEnv -> ValueEnv
bindSuperStub m cls scls = bindEntity m f $ Value f False 1 $ polyType ty
  where f  = qSuperDictStubId cls scls
        ty = superDictStubType cls scls (TypeVariable 0)

bindInstDecls :: ModuleIdent -> TCEnv -> ClassEnv -> InstEnv -> ValueEnv
                  -> ValueEnv
bindInstDecls m tcEnv clsEnv =
  flip (foldr $ bindInstFuns m tcEnv clsEnv) . Map.toList

bindInstFuns :: ModuleIdent -> TCEnv -> ClassEnv -> (InstIdent, InstInfo)
             -> ValueEnv -> ValueEnv
bindInstFuns m tcEnv clsEnv ((cls, tc), (m', ps, is)) =
  bindInstDict m cls ty m' ps . bindInstMethods m clsEnv cls ty m' ps is
  where ty = applyType (TypeConstructor tc) (take n (map TypeVariable [0..]))
        n = kindArity (tcKind m tc tcEnv) - kindArity (clsKind m cls tcEnv)

bindInstDict :: ModuleIdent -> QualIdent -> Type -> ModuleIdent -> PredSet
             -> ValueEnv -> ValueEnv
bindInstDict m cls ty m' ps =
  bindMethod m (qInstFunId m' cls ty) 0 $ PredType ps $ dictType $ Pred cls ty

bindInstMethods :: ModuleIdent -> ClassEnv -> QualIdent -> Type -> ModuleIdent
                -> PredSet -> [(Ident, Int)] -> ValueEnv -> ValueEnv
bindInstMethods m clsEnv cls ty m' ps is =
  flip (foldr (bindInstMethod m cls ty m' ps is)) (classMethods cls clsEnv)

bindInstMethod :: ModuleIdent -> QualIdent -> Type -> ModuleIdent
               -> PredSet -> [(Ident, Int)] -> Ident -> ValueEnv -> ValueEnv
bindInstMethod m cls ty m' ps is f vEnv = bindMethod m f' a pty vEnv
  where f'  = qImplMethodId m' cls ty f
        a   = fromMaybe 0 $ lookup f is
        pty = instMethodType vEnv ps cls ty f

bindMethod :: ModuleIdent -> QualIdent -> Int -> PredType -> ValueEnv
           -> ValueEnv
bindMethod m f n pty = bindEntity m f $ Value f False n $ typeScheme pty

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
dictTransDataConstr (DataConstr c n ps tys) =
  DataConstr c n emptyPredSet $ map dictType (Set.toAscList ps) ++ tys
dictTransDataConstr (RecordConstr c n ps _ tys) =
  dictTransDataConstr $ DataConstr c n ps tys

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
dictTransValueInfo (DataConstructor c a ls (ForAllExist n n' pty)) =
  DataConstructor c a' ls' $ ForAllExist n n' $ predType ty
  where a'  = arrowArity ty
        ls' = replicate (a' - a) anonId ++ ls
        ty  = transformPredType pty
dictTransValueInfo (NewtypeConstructor c l (ForAllExist n n' pty)) =
  NewtypeConstructor c l (ForAllExist n n' (predType (unpredType pty)))
dictTransValueInfo (Value f cm a (ForAll n pty)) =
  Value f False a' $ ForAll n $ predType ty
  where a' = a + if cm then 1 else arrowArity ty - arrowArity (unpredType pty)
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
dictExports (ClassDecl _ _ cls _ _) = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  return $ classExports m clsEnv cls
dictExports (InstanceDecl _ _ cls ty _) = do
  m <- getModuleIdent
  clsEnv <- getClassEnv
  return $ instExports m clsEnv cls (toType [] ty)
dictExports _ = return []

classExports :: ModuleIdent -> ClassEnv -> Ident -> [Export]
classExports m clsEnv cls =
  ExportTypeWith (qDictTypeId qcls) [dictConstrId qcls] :
    map (Export . qSuperDictStubId qcls) (superClasses qcls clsEnv) ++
      map (Export . qDefaultMethodId qcls) (classMethods qcls clsEnv)
  where qcls = qualifyWith m cls

instExports :: ModuleIdent -> ClassEnv -> QualIdent -> Type -> [Export]
instExports m clsEnv cls ty =
  Export (qInstFunId m cls ty) :
    map (Export . qImplMethodId m cls ty) (classMethods cls clsEnv)

-- -----------------------------------------------------------------------------
-- Transforming the module
-- -----------------------------------------------------------------------------

type DictEnv = [(Pred, Expression Type)]

emptyDictEnv :: DictEnv
emptyDictEnv = []

class DictTrans a where
  dictTrans :: a PredType -> DTM (a Type)

instance DictTrans Module where
  dictTrans (Module ps m es is ds) = do
    liftedDs <- concatMapM liftDecls ds
    stubDs <- concatMapM createStubs ds
    tcEnv <- getTyConsEnv
    clsEnv <- getClassEnv
    inEnv <- getInstEnv
    modifyValueEnv $ bindClassDecls m tcEnv clsEnv
    modifyValueEnv $ bindInstDecls m tcEnv clsEnv inEnv
    modifyTyConsEnv $ bindDictTypes m clsEnv
    transDs <- mapM dictTrans liftedDs
    modifyValueEnv $ dictTransValues
    modifyTyConsEnv $ dictTransTypes
    dictEs <- addExports es <$> concatMapM dictExports ds
    return $ Module ps m dictEs is $ transDs ++ stubDs

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
    VariablePattern pty@(PredType ps _) v | not (Set.null ps) ->
      dictTrans $ FunctionDecl p pty v [Equation p (FunLhs v []) rhs]
    _ -> withLocalDictEnv $ PatternDecl p <$> dictTrans t <*> dictTrans rhs
  dictTrans (FreeDecl                 p vs) =
    return $ FreeDecl p $ map (fmap unpredType) vs
  dictTrans (ExternalDecl             p vs) =
    return $ ExternalDecl p $ map (fmap unpredType) vs
  dictTrans d                               =
    internalError $ "Dictionary.dictTrans: " ++ show d

dictTransConstrDecl :: [Ident] -> ConstrDecl -> DataConstr -> ConstrDecl
dictTransConstrDecl tvs (ConstrDecl p evs _ c tes) dc =
  ConstrDecl p evs [] c $ map (fromType $ tvs ++ evs ++ bvs) tys
  where DataConstr _ _ _ tys = dictTransDataConstr dc
        bvs = nub $ bv tes
dictTransConstrDecl tvs (ConOpDecl p evs cx ty1 op ty2) dc =
  dictTransConstrDecl tvs (ConstrDecl p evs cx op [ty1, ty2]) dc
dictTransConstrDecl _ d _ = internalError $ "Dictionary.dictTrans: " ++ show d

instance DictTrans Equation where
  dictTrans (Equation p (FunLhs f ts) rhs) = withLocalValueEnv $ do
    m <- getModuleIdent
    pls <- matchPredList (varType m f) $
             foldr (TypeArrow . typeOf) (typeOf rhs) ts
    ts' <- addDictArgs pls ts
    modifyValueEnv $ bindPatterns ts'
    Equation p (FunLhs f ts') <$> dictTrans rhs
  dictTrans eq                             =
    internalError $ "Dictionary.dictTrans: " ++ show eq

instance DictTrans Rhs where
  dictTrans (SimpleRhs p e []) = simpleRhs p <$> dictTrans e
  dictTrans rhs                =
    internalError $ "Dictionary.dictTrans: " ++ show rhs

instance DictTrans Pattern where
  dictTrans (LiteralPattern        pty l) =
    return $ LiteralPattern (unpredType pty) l
  dictTrans (VariablePattern       pty v) =
    return $ VariablePattern (unpredType pty) v
  dictTrans (ConstructorPattern pty c ts) = do
    pls <- matchPredList (conType c) $
             foldr (TypeArrow . typeOf) (unpredType pty) ts
    ConstructorPattern (unpredType pty) c <$> addDictArgs pls ts
  dictTrans (AsPattern               v t) = AsPattern v <$> dictTrans t
  dictTrans t                             =
    internalError $ "Dictionary.dictTrans: " ++ show t

instance DictTrans Expression where
  dictTrans (Literal     pty l) = return $ Literal (unpredType pty) l
  dictTrans (Variable    pty v) = do
    pls <- matchPredList (funType v) (unpredType pty)
    es <- mapM dictArg pls
    let ty = foldr (TypeArrow . typeOf) (unpredType pty) es
    return $ apply (Variable ty v) es
  dictTrans (Constructor pty c) = do
    pls <- matchPredList (conType c) (unpredType pty)
    es <- mapM dictArg pls
    let ty = foldr (TypeArrow . typeOf) (unpredType pty) es
    return $ apply (Constructor ty c) es
  dictTrans (Apply       e1 e2) =
    Apply <$> dictTrans e1 <*> dictTrans e2
  dictTrans (Typed       e qty) =
    Typed <$> dictTrans e <*> dictTransQualTypeExpr qty
  dictTrans (Lambda       ts e) = withLocalValueEnv $ withLocalDictEnv $ do
    ts' <- mapM dictTrans ts
    modifyValueEnv $ bindPatterns ts'
    Lambda ts' <$> dictTrans e
  dictTrans (Let          ds e) = withLocalValueEnv $ do
    modifyValueEnv $ bindDecls ds
    Let <$> mapM dictTrans ds <*> dictTrans e
  dictTrans (Case      ct e as) =
    Case ct <$> dictTrans e <*> mapM dictTrans as
  dictTrans e                   =
    internalError $ "Dictionary.dictTrans: " ++ show e

-- Just like before in desugaring, we ignore the context in the type signature
-- of a typed expression, since there should be no possibility to provide an
-- non-empty context without scoped type-variables.
-- TODO: Verify

dictTransQualTypeExpr :: QualTypeExpr -> DTM QualTypeExpr
dictTransQualTypeExpr (QualTypeExpr _ ty) = return $ QualTypeExpr [] ty

instance DictTrans Alt where
  dictTrans (Alt p t rhs) = withLocalValueEnv $ withLocalDictEnv $ do
    t' <- dictTrans t
    modifyValueEnv $ bindPattern t'
    Alt p t' <$> dictTrans rhs

addDictArgs :: [Pred] -> [Pattern PredType] -> DTM [Pattern Type]
addDictArgs pls ts = do
  dictVars <- mapM (freshVar "_#dict" . dictType) pls
  clsEnv <- getClassEnv
  modifyDictEnv $ (++) $ dicts clsEnv $ zip pls (map (uncurry mkVar) dictVars)
  (++) (map (uncurry VariablePattern) dictVars) <$> mapM dictTrans ts
  where dicts clsEnv vs
          | null vs = vs
          | otherwise = vs ++ dicts clsEnv (concatMap (superDicts clsEnv) vs)
        superDicts clsEnv (Pred cls ty, e) =
          map (superDict cls ty e) (superClasses cls clsEnv)
        superDict cls ty e scls =
          (Pred scls ty, Apply (superDictExpr cls scls ty) e)
        superDictExpr cls scls ty =
          Variable (superDictStubType cls scls ty) (qSuperDictStubId cls scls)

-- The function 'dictArg' constructs the dictionary argument for a predicate
-- from the predicates of a class method or an overloaded function. It checks
-- whether a dictionary for the predicate is available in the dictionary
-- environment, which is the case when the predicate's type is a type variable,
-- and uses 'instDict' otherwise in order to supply a new dictionary using the
-- appropriate instance dictionary construction function. If the corresponding
-- instance declaration has a non-empty context, the dictionary construction
-- function is applied to the dictionaries computed for the context instantiated
-- at the appropriate types.

dictArg :: Pred -> DTM (Expression Type)
dictArg p = maybeM (instDict p) return (lookup p <$> getDictEnv)

instDict :: Pred -> DTM (Expression Type)
instDict p = instPredList p >>= flip (uncurry instFunApp) p

instFunApp :: ModuleIdent -> [Pred] -> Pred -> DTM (Expression Type)
instFunApp m pls p@(Pred cls ty) = apply (Variable ty' f) <$> mapM dictArg pls
  where f   = qInstFunId m cls ty
        ty' = foldr1 TypeArrow $ map dictType $ pls ++ [p]

instPredList :: Pred -> DTM (ModuleIdent, [Pred])
instPredList (Pred cls ty) = case unapplyType True ty of
  (TypeConstructor tc, tys) -> do
    inEnv <- getInstEnv
    case lookupInstInfo (cls, tc) inEnv of
      Just (m, ps, _) -> return (m, expandAliasType tys $ Set.toAscList ps)
      Nothing -> internalError $ "Dictionary.instPredList: " ++ show (cls, tc)
  _ -> internalError $ "Dictionary.instPredList: " ++ show ty

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
                 (splits $ Set.toAscList ps)

qualMatch :: [Pred] -> Type -> [Pred] -> Type -> Maybe [Pred]
qualMatch pls1 ty1 pls2 ty2 = case predListMatch pls2 ty2 of
  Just ty2' -> Just $ subst (matchType ty1 ty2' idSubst) pls1
  Nothing -> Nothing

predListMatch :: [Pred] -> Type -> Maybe Type
predListMatch []     ty = Just ty
predListMatch (p:ps) ty = case ty of
  TypeForall _ ty'                                 -> predListMatch (p : ps) ty'
  TypeArrow ty1 ty2 | ty1 == dictType (instPred p) -> predListMatch ps ty2
  _                                                -> Nothing

splits :: [a] -> [([a], [a])]
splits xs = zip (inits xs) (tails xs)

-- -----------------------------------------------------------------------------
-- Optimizing method calls
-- -----------------------------------------------------------------------------

-- Whenever a type class method is applied at a known type, the compiler can
-- apply the type instance's implementation directly.

type SpecEnv = Map.Map (QualIdent, QualIdent) QualIdent

emptySpEnv :: SpecEnv
emptySpEnv = Map.empty

initSpEnv :: ClassEnv -> InstEnv -> SpecEnv
initSpEnv clsEnv = foldr (uncurry bindInstance) emptySpEnv . Map.toList
  where bindInstance (cls, tc) (m, _, _) =
          flip (foldr $ bindInstanceMethod m cls tc) $ classMethods cls clsEnv
        bindInstanceMethod m cls tc f = Map.insert (f', d) f''
          where f'  = qualifyLike cls f
                d   = qInstFunId m cls ty
                f'' = qImplMethodId m cls ty f
                ty  = TypeConstructor tc

class Specialize a where
  specialize :: a Type -> DTM (a Type)

instance Specialize Module where
  specialize (Module ps m es is ds) = do
    clsEnv <- getClassEnv
    inEnv <- getInstEnv
    setSpEnv $ initSpEnv clsEnv inEnv
    Module ps m es is <$> mapM specialize ds

instance Specialize Decl where
  specialize (FunctionDecl p ty f eqs) =
    FunctionDecl p ty f <$> mapM specialize eqs
  specialize (PatternDecl     p t rhs) = PatternDecl p t <$> specialize rhs
  specialize d                         = return d

instance Specialize Equation where
  specialize (Equation p lhs rhs) = Equation p lhs <$> specialize rhs

instance Specialize Rhs where
  specialize (SimpleRhs p e []) = simpleRhs p <$> specialize e
  specialize rhs                =
    internalError $ "Dictionary.specialize: " ++ show rhs

instance Specialize Expression where
  specialize e = specialize' e []

specialize' :: Expression Type -> [Expression Type] -> DTM (Expression Type)
specialize' l@(Literal     _ _) es = return $ apply l es
specialize' v@(Variable   _ v') es = do
  spEnv <- getSpEnv
  return $ case Map.lookup (v', f) spEnv of
    Just f' -> apply (Variable ty' f') $ es'' ++ es'
    Nothing -> apply v es
  where d:es' = es
        (Variable _ f, es'') = unapply d []
        ty' = foldr (TypeArrow . typeOf) (typeOf $ Apply v d) es''
specialize' c@(Constructor _ _) es = return $ apply c es
specialize' (Typed       e qty) es = do
  e' <- specialize e
  return $ apply (Typed e' qty) es
specialize' (Apply       e1 e2) es = do
  e2' <- specialize e2
  specialize' e1 $ e2' : es
specialize' (Lambda       ts e) es = do
  e' <- specialize e
  return $ apply (Lambda ts e') es
specialize' (Let          ds e) es = do
  ds' <- mapM specialize ds
  e' <- specialize e
  return $ apply (Let ds' e') es
specialize' (Case      ct e as) es = do
  e' <- specialize e
  as' <- mapM specialize as
  return $ apply (Case ct e' as') es
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
-- from the precedence environment as functions with class constraint have
-- been supplemented with addiontal dictionary arguments during the dictionary
-- transformation.

cleanup :: Module a -> DTM (Module a)
cleanup (Module ps m es is ds) = do
  cleanedEs <- traverse cleanupExportSpec es
  cleanedDs <- concatMapM cleanupInfixDecl ds
  cleanupTyConsEnv
  cleanupPrecEnv
  return $ Module ps m cleanedEs is cleanedDs

cleanupExportSpec :: ExportSpec -> DTM ExportSpec
cleanupExportSpec (Exporting p es) = Exporting p <$> concatMapM cleanupExport es

cleanupExport :: Export -> DTM [Export]
cleanupExport e@(Export             _) = return [e]
cleanupExport e@(ExportTypeWith tc cs) = do
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo tc tcEnv of
    [TypeClass _ _ _] -> return $ map (Export . qualifyLike tc) cs
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
dictTransIDecl _ _    _      (HidingClassDecl  p _ cls k tv) =
  [HidingDataDecl p (qDictTypeId cls) (fmap (flip ArrowKind Star) k) [tv]]
dictTransIDecl m vEnv clsEnv (IClassDecl   p _ cls k _ _ hs) =
  dictDecl : defaults ++ methodStubs ++ superDictStubs
  where qcls  = qualQualify m cls
        sclss = superClasses qcls clsEnv
        ms    = classMethods qcls clsEnv
        dictDecl    = IDataDecl p (qDictTypeId cls)
                        (fmap (flip ArrowKind Star) k)
                        [head identSupply] [constrDecl] []
        constrDecl  = iConstrDeclFromDataConstructor m vEnv $ qDictConstrId qcls
        defaults    = map (iFunctionDeclFromValue m vEnv .
                            qDefaultMethodId qcls) ms
        methodStubs = map (iFunctionDeclFromValue m vEnv . qualifyLike qcls) $
                        filter (`notElem` hs) ms
        superDictStubs = map (iFunctionDeclFromValue m vEnv .
                               qSuperDictStubId qcls) sclss
dictTransIDecl m vEnv clsEnv (IInstanceDecl _ _ cls ty _ mm) =
  iFunctionDeclFromValue m vEnv (qInstFunId m' qcls ty') :
    map (iFunctionDeclFromValue m vEnv . qImplMethodId m' qcls ty') ms
  where m'   = fromMaybe m mm
        qcls = qualQualify m cls
        ty'  = toQualType m [] ty
        ms   = classMethods qcls clsEnv

dictTransIConstrDecl :: ModuleIdent -> [Ident] -> ConstrDecl -> ConstrDecl
dictTransIConstrDecl m tvs (ConstrDecl     p evs cx c tys) =
  ConstrDecl p evs [] c $ transformIContext m (tvs ++ evs) cx ++ tys
dictTransIConstrDecl m tvs (ConOpDecl p evs cx ty1 op ty2) =
  dictTransIConstrDecl m tvs (ConstrDecl p evs cx op [ty1, ty2])
dictTransIConstrDecl m tvs (RecordDecl      p evs cx c fs) =
  RecordDecl p evs [] c $
    map toFieldDecl (transformIContext m (tvs ++ evs) cx) ++ fs
  where toFieldDecl = FieldDecl NoPos [anonId]

transformIContext :: ModuleIdent -> [Ident] -> Context -> [TypeExpr]
transformIContext m tvs cx =
   map (fromQualType m tvs . dictType) (Set.toAscList $ toQualPredSet m tvs cx)

iFunctionDeclFromValue :: ModuleIdent -> ValueEnv -> QualIdent -> IDecl
iFunctionDeclFromValue m vEnv f = case qualLookupValue f vEnv of
  [Value _ _ a (ForAll _ pty)] ->
    IFunctionDecl NoPos (qualUnqualify m f) Nothing a $
      fromQualPredType m identSupply pty
  _ -> internalError $ "Dictionary.iFunctionDeclFromValue: " ++ show f

iConstrDeclFromDataConstructor :: ModuleIdent -> ValueEnv -> QualIdent
                               -> ConstrDecl
iConstrDeclFromDataConstructor m vEnv c = case qualLookupValue c vEnv of
  [DataConstructor _ _ _ (ForAllExist n n' pty)] ->
    ConstrDecl NoPos evs [] (unqualify c) tys
    where evs = take n' $ drop n identSupply
          tys = map (fromQualType m identSupply) $ arrowArgs $ unpredType pty
  _ -> internalError $ "Dictionary.iConstrDeclFromDataConstructor: " ++ show c

-- -----------------------------------------------------------------------------
-- Functions for naming newly created types, functions and parameters
-- -----------------------------------------------------------------------------

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

superDictStubId :: QualIdent -> QualIdent -> Ident
superDictStubId cls scls = mkIdent $
  "_super#" ++ qualName cls ++ '#' : qualName scls

qSuperDictStubId :: QualIdent -> QualIdent -> QualIdent
qSuperDictStubId cls = qualifyLike cls . superDictStubId cls

instFunId :: QualIdent -> Type -> Ident
instFunId cls ty = mkIdent $
  "_inst#" ++ qualName cls ++ '#' : qualName (rootOfType ty)

qInstFunId :: ModuleIdent -> QualIdent -> Type -> QualIdent
qInstFunId m cls = qualifyWith m . instFunId cls

implMethodId :: QualIdent -> Type -> Ident -> Ident
implMethodId cls ty f = mkIdent $
  "_impl#" ++ idName f ++ '#' : qualName cls ++ '#' : qualName (rootOfType ty)

qImplMethodId :: ModuleIdent -> QualIdent -> Type -> Ident -> QualIdent
qImplMethodId m cls ty = qualifyWith m . implMethodId cls ty

-- -----------------------------------------------------------------------------
-- Generating variables
-- -----------------------------------------------------------------------------

freshVar :: String -> Type -> DTM (Type, Ident)
freshVar name ty = ((,) ty) . mkIdent . (name ++) .  show <$> getNextId

-- -----------------------------------------------------------------------------
-- Auxiliary functions
-- -----------------------------------------------------------------------------

-- The function 'dictType' returns the type of the dictionary corresponding to
-- a particular C-T instance.

dictType :: Pred -> Type
dictType (Pred cls ty) = TypeApply (TypeConstructor $ qDictTypeId cls) ty

-- The function 'transformPredType' replaces each predicate with a new
-- dictionary type argument.

transformPredType :: PredType -> Type
transformPredType (PredType ps ty) =
  foldr (TypeArrow . dictType) ty $ Set.toList ps

-- The function 'transformMethodPredType' first deletes the implicit class
-- constraint and then transforms the resulting predicated type as above.

transformMethodPredType :: PredType -> Type
transformMethodPredType (PredType ps ty) =
  transformPredType $ PredType (Set.deleteMin ps) ty

-- The function 'generalizeMethodType' generalizes an already transformed
-- method type to a forall type by quantifying all occuring type variables
-- except for the class variable whose index is 0.
generalizeMethodType :: Type -> Type
generalizeMethodType ty
  | null tvs  = ty
  | otherwise = TypeForall tvs ty
  where tvs = nub $ filter (/= 0) $ typeVars ty

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
instPred (Pred cls ty) = Pred cls (instType ty)

unRenameIdentIf :: Bool -> Ident -> Ident
unRenameIdentIf b = if b then unRenameIdent else id

-- The string for the error message for a class method's default method
-- implementation has to be constructed in its desugared form since the
-- desugaring has already taken place.

preludeError :: Type -> String -> Expression PredType
preludeError a =
  Apply (Variable (predType (TypeArrow stringType a)) qErrorId) . stringExpr

stringExpr :: String -> Expression PredType
stringExpr = foldr (consExpr . Literal (predType charType) . Char) nilExpr
  where
  nilExpr = Constructor (predType stringType) qNilId
  consExpr = Apply . Apply (Constructor (predType $ consType charType) qConsId)

-- The function 'varType' is able to lookup both local and global identifiers.
-- Since the environments have been qualified before, global declarations are
-- only visible under their original name whereas local declarations are always
-- entered unqualified.

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
  [DataConstructor  _ _ _ (ForAllExist n _ pty)] -> ForAll n pty
  [NewtypeConstructor _ _ (ForAllExist n _ pty)] -> ForAll n pty
  _ -> internalError $ "Dictionary.conType: " ++ show c

funType :: QualIdent -> ValueEnv -> TypeScheme
funType f vEnv = case qualLookupValue f vEnv of
  [Value _ _ _ tySc] -> tySc
  [Label _ _   tySc] -> tySc
  _ -> internalError $ "Dictionary.funType " ++ show f

opType :: QualIdent -> ValueEnv -> TypeScheme
opType op vEnv = case qualLookupValue op vEnv of
  [DataConstructor  _ _ _ (ForAllExist n _ pty)] -> ForAll n pty
  [NewtypeConstructor _ _ (ForAllExist n _ pty)] -> ForAll n pty
  [Value _ _ _                             tySc] -> tySc
  [Label _ _                               tySc] -> tySc
  _ -> internalError $ "Dictionary.opType " ++ show op
