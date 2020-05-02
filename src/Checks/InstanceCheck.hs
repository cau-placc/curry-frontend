{- |
    Module      :  $Header$
    Description :  Checks instances
    Copyright   :  (c)        2016 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   Before type checking, the compiler checks for every instance declaration
   that all necessary super class instances exist. Furthermore, the compiler
   infers the contexts of the implicit instance declarations introduced by
   deriving clauses in data and newtype declarations. The instances declared
   explicitly and automatically derived by the compiler are added to the
   instance environment . It is also checked that there are no duplicate
   instances and that all types specified in a default declaration are
   instances of the Num class.
-}
module Checks.InstanceCheck (instanceCheck) where

import           Control.Monad.Extra        (concatMapM, whileM, unless)
import qualified Control.Monad.State as S   (State, execState, gets, modify)
import           Data.List                  (nub, partition, sortBy)
import qualified Data.Map            as Map
import qualified Data.Set.Extra      as Set

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Base.SpanInfo
import Curry.Syntax hiding (impls)
import Curry.Syntax.Pretty

import Base.CurryTypes
import Base.Messages (Message, spanInfoMessage, message, internalError)
import Base.SCC (scc)
import Base.TypeExpansion
import Base.Types
import Base.TypeSubst
import Base.Utils (fst3, snd3, findMultiples)

import Env.Class
import Env.Instance
import Env.TypeConstructor

instanceCheck :: ModuleIdent -> TCEnv -> ClassEnv -> InstEnv -> [Decl a]
              -> (InstEnv, [Message])
instanceCheck m tcEnv clsEnv inEnv ds =
  case findMultiples (local ++ imported) of
    [] -> execINCM (checkDecls tcEnv clsEnv ds) state
    iss -> (inEnv, map (errMultipleInstances tcEnv) iss)
  where
    local = map (flip InstSource m) $ concatMap (genInstIdents m tcEnv) ds
    imported = map (uncurry InstSource . fmap fst3) $ Map.toList inEnv
    state = INCState m inEnv []

-- In order to provide better error messages, we use the following data type
-- to keep track of an instance's source, i.e., the module it was defined in.

data InstSource = InstSource InstIdent ModuleIdent

instance Eq InstSource where
  InstSource i1 _ == InstSource i2 _ = i1 == i2

-- |Instance Check Monad
type INCM = S.State INCState

-- |Internal state of the Instance Check
data INCState = INCState
  { moduleIdent :: ModuleIdent
  , instEnv     :: InstEnv
  , errors      :: [Message]
  }

execINCM :: INCM a -> INCState -> (InstEnv, [Message])
execINCM incm s =
  let s' = S.execState incm s in (instEnv s', reverse $ nub $ errors s')

getModuleIdent :: INCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getInstEnv :: INCM InstEnv
getInstEnv = S.gets instEnv

modifyInstEnv :: (InstEnv -> InstEnv) -> INCM ()
modifyInstEnv f = S.modify $ \s -> s { instEnv = f $ instEnv s }

report :: Message -> INCM ()
report err = S.modify (\s -> s { errors = err : errors s })

ok :: INCM ()
ok = return ()

checkDecls :: TCEnv -> ClassEnv -> [Decl a] -> INCM ()
checkDecls tcEnv clsEnv ds = do
  mapM_ (bindInstance tcEnv clsEnv) ids
  mapM (declDeriveDataInfo tcEnv clsEnv) (filter isDataDecl tds) >>=
    mapM_ (bindDerivedInstances clsEnv) . groupDeriveInfos
  mapM (declDeriveInfo tcEnv clsEnv) (filter hasDerivedInstances tds) >>=
    mapM_ (bindDerivedInstances clsEnv) . groupDeriveInfos
  mapM_ (checkInstance tcEnv clsEnv) ids
  mapM_ (checkDefault tcEnv clsEnv) dds
  where (tds, ods) = partition isTypeDecl ds
        ids = filter isInstanceDecl ods
        dds = filter isDefaultDecl ods
        isDataDecl (DataDecl    _ _ _ _ _) = True
        isDataDecl (NewtypeDecl _ _ _ _ _) = True
        isDataDecl _                       = False

-- First, the compiler adds all explicit instance declarations to the
-- instance environment.

bindInstance :: TCEnv -> ClassEnv -> Decl a -> INCM ()
bindInstance tcEnv clsEnv (InstanceDecl _ _ cx qcls inst ds) = do
  m <- getModuleIdent
  let TypeContext ps _ = expandPolyType m tcEnv clsEnv $
                           ContextType NoSpanInfo cx inst
  modifyInstEnv $
    bindInstInfo (genInstIdent m tcEnv qcls inst) (m, ps, impls [] ds)
  where impls is [] = is
        impls is (FunctionDecl _ _ f eqs:ds')
          | f' `elem` map fst is = impls is ds'
          | otherwise            = impls ((f', eqnArity $ head eqs) : is) ds'
          where f' = unRenameIdent f
        impls _ _ = internalError "InstanceCheck.bindInstance.impls"
bindInstance _     _      _                                = ok

-- Next, the compiler sorts the data and newtype declarations with non-empty
-- deriving clauses into minimal binding groups and infers contexts for their
-- instance declarations. In the case of (mutually) recursive data types,
-- inference of the appropriate contexts may require a fixpoint calculation.

hasDerivedInstances :: Decl a -> Bool
hasDerivedInstances (DataDecl    _ _ _ _ clss) = not $ null clss
hasDerivedInstances (NewtypeDecl _ _ _ _ clss) = not $ null clss
hasDerivedInstances _                          = False

-- For the purposes of derived instances, a newtype declaration is treated
-- as a data declaration with a single constructor. The compiler also sorts
-- derived classes with respect to the super class hierarchy so that subclass
-- instances are added to the instance environment after their super classes.

data DeriveInfo = DeriveInfo Position QualIdent Type [Type] [QualIdent]

declDeriveInfo :: TCEnv -> ClassEnv -> Decl a -> INCM DeriveInfo
declDeriveInfo tcEnv clsEnv (DataDecl p tc tvs cs clss) =
  mkDeriveInfo tcEnv clsEnv p tc tvs (concat tyss) clss
  where tyss = map constrDeclTypes cs
        constrDeclTypes (ConstrDecl     _ _ tys) = tys
        constrDeclTypes (ConOpDecl  _ ty1 _ ty2) = [ty1, ty2]
        constrDeclTypes (RecordDecl      _ _ fs) = tys
          where tys = [ty | FieldDecl _ ls ty <- fs, _ <- ls]
declDeriveInfo tcEnv clsEnv (NewtypeDecl p tc tvs nc clss) =
  mkDeriveInfo tcEnv clsEnv p tc tvs [nconstrType nc] clss
declDeriveInfo _ _ _ =
  internalError "InstanceCheck.declDeriveInfo: no data or newtype declaration"

declDeriveDataInfo :: TCEnv -> ClassEnv -> Decl a -> INCM DeriveInfo
declDeriveDataInfo tcEnv clsEnv (DataDecl p tc tvs cs _) =
  mkDeriveDataInfo tcEnv clsEnv p tc tvs (concat tyss)
  where tyss = map constrDeclTypes cs
        constrDeclTypes (ConstrDecl     _ _ tys) = tys
        constrDeclTypes (ConOpDecl  _ ty1 _ ty2) = [ty1, ty2]
        constrDeclTypes (RecordDecl      _ _ fs) = tys
          where tys = [ty | FieldDecl _ ls ty <- fs, _ <- ls]
declDeriveDataInfo tcEnv clsEnv (NewtypeDecl p tc tvs nc _) =
  mkDeriveDataInfo tcEnv clsEnv p tc tvs [nconstrType nc]
declDeriveDataInfo _ _ _ = internalError
  "InstanceCheck.declDeriveDataInfo: no data or newtype declaration"

mkDeriveInfo :: TCEnv -> ClassEnv -> SpanInfo -> Ident -> [Ident]
             -> [TypeExpr] -> [QualIdent] -> INCM DeriveInfo
mkDeriveInfo tcEnv clsEnv spi tc tvs tys clss = do
  m <- getModuleIdent
  let otc = qualifyWith m tc
      oclss = map (flip (getOrigName m) tcEnv) clss
      TypeContext ps ty = expandConstrType m tcEnv clsEnv otc tvs tys
      (tys', ty') = arrowUnapply ty
  return $ DeriveInfo p otc (TypeContext ps ty') tys' $ sortClasses clsEnv oclss
  where p = spanInfo2Pos spi

mkDeriveDataInfo :: TCEnv -> ClassEnv -> SpanInfo -> Ident -> [Ident]
                 -> [TypeExpr] -> INCM DeriveInfo
mkDeriveDataInfo tcEnv clsEnv spi tc tvs tys = do
  m <- getModuleIdent
  let otc = qualifyWith m tc
      TypeContext ps ty = expandConstrType m tcEnv clsEnv otc tvs tys
      (tys', ty') = arrowUnapply ty
  return $ DeriveInfo p otc (TypeContext ps ty') tys' [qDataId]
  where p = spanInfo2Pos spi

sortClasses :: ClassEnv -> [QualIdent] -> [QualIdent]
sortClasses clsEnv clss = map fst $ sortBy compareDepth $ map adjoinDepth clss
  where (_, d1) `compareDepth` (_, d2) = d1 `compare` d2
        adjoinDepth cls = (cls, length $ allSuperClasses cls clsEnv)

groupDeriveInfos :: [DeriveInfo] -> [[DeriveInfo]]
groupDeriveInfos = scc bound free
  where bound (DeriveInfo _ tc _ _ _) = [tc]
        free (DeriveInfo _ _ _ tys _) = concatMap typeConstrs tys

bindDerivedInstances :: ClassEnv -> [DeriveInfo] -> INCM ()
bindDerivedInstances clsEnv dis = unless (any hasDataFunType dis) $ do
  mapM_ (enterInitialPredSet clsEnv) dis
  whileM $ concatMapM (inferPredSets clsEnv) dis >>= updatePredSets
  where
    hasDataFunType (DeriveInfo _ _ _ tys clss) =
      clss == [qDataId] && any isFunType tys

enterInitialPredSet :: ClassEnv -> DeriveInfo -> INCM ()
enterInitialPredSet clsEnv (DeriveInfo _ tc pty _ clss) =
  mapM_ (bindDerivedInstance clsEnv tc tc pty) clss

-- Note: The methods and arities entered into the instance environment have
-- to match methods and arities of the later generated instance declarations.

bindDerivedInstance :: HasSpanInfo s => ClassEnv -> s -> QualIdent -> Type -> QualIdent
                    -> INCM ()
bindDerivedInstance clsEnv p tc pty cls = do
  m <- getModuleIdent
  ((i, ps), _) <- inferPredSet clsEnv p tc pty [] cls
  modifyInstEnv (bindInstInfo i (m, ps, impls))
  where impls | cls == qEqId      = [(eqOpId, 2)]
              | cls == qOrdId     = [(leqOpId, 2)]
              | cls == qEnumId    = [ (succId, 1), (predId, 1), (toEnumId, 1)
                                    , (fromEnumId, 1), (enumFromId, 1)
                                    , (enumFromThenId, 2)
                                    ]
              | cls == qBoundedId = [(maxBoundId, 0), (minBoundId, 0)]
              | cls == qReadId    = [(readsPrecId, 2)]
              | cls == qShowId    = [(showsPrecId, 2)]
              | cls == qDataId    = [(dataEqId, 2), (aValueId, 0)]
              | otherwise         =
                internalError "InstanceCheck.bindDerivedInstance.impls"

inferPredSets :: ClassEnv -> DeriveInfo -> INCM [((InstIdent, PredSet), Bool)]
inferPredSets clsEnv (DeriveInfo _ tc pty tys clss) =
  mapM (inferPredSet clsEnv tc tc pty tys) clss

inferPredSet :: HasSpanInfo s => ClassEnv -> s -> QualIdent -> Type -> [Type]
             -> QualIdent -> INCM ((InstIdent, PredSet), Bool)
inferPredSet clsEnv p tc (TypeContext ps inst) tys cls = do
  m <- getModuleIdent
  let doc = ppPred m $ Pred cls inst
      sclss = superClasses cls clsEnv
      ps'   = Set.fromList [Pred cls ty | ty <- tys]
      ps''  = Set.fromList [Pred scls inst | scls <- sclss]
      ps''' = ps `Set.union` ps' `Set.union` ps''
  (ps4, novarps) <-
    reducePredSet (cls == qDataId) p "derived instance" doc clsEnv ps'''
  let ps5 = filter noPolyPred $ Set.toList ps4
  if any (isDataPred m) (Set.toList novarps ++ ps5) && cls == qDataId
    then return    (((cls, tc), ps4), False)
    else mapM_ (reportUndecidable p "derived instance" doc) ps5
         >> return (((cls, tc), ps4), True)
  where
    noPolyPred (Pred _ (TypeVariable _)) = False
    noPolyPred (Pred _ _               ) = True
    isDataPred _ (Pred qid _) = qid == qDataId
inferPredSet _ _ _ _ _ _ = internalError "InstanceCheck.inferPredSet"

updatePredSets :: [((InstIdent, PredSet), Bool)] -> INCM Bool
updatePredSets = fmap or . mapM (uncurry updatePredSet)

updatePredSet :: (InstIdent, PredSet) -> Bool -> INCM Bool
updatePredSet (i, ps) enter = do
  inEnv <- getInstEnv
  case lookupInstInfo i inEnv of
    Just (m, ps', is)
      | not enter -> modifyInstEnv (removeInstInfo i) >> return False
      | ps == ps' -> return False
      | otherwise -> do
        modifyInstEnv $ bindInstInfo i (m, ps, is)
        return True
    Nothing -> internalError "InstanceCheck.updatePredSet"

reportUndecidable :: HasSpanInfo s => s -> String -> Doc -> Pred -> INCM ()
reportUndecidable p what doc predicate@(Pred _ ty) = do
  m <- getModuleIdent
  case ty of
    TypeVariable _ -> return ()
    _ -> report $ errMissingInstance m p what doc predicate

-- Then, the compiler checks the contexts of all explicit instance
-- declarations to detect missing super class instances. For an instance
-- declaration
--
-- instance cx => C (T u_1 ... u_k) where ...
--
-- the compiler ensures that T is an instance of all of C's super classes
-- and also that the contexts of the corresponding instance declarations are
-- satisfied by cx.

checkInstance :: TCEnv -> ClassEnv -> Decl a -> INCM ()
checkInstance tcEnv clsEnv (InstanceDecl _ _ cx cls inst _) = do
  m <- getModuleIdent
  let TypeContext ps ty = expandPolyType m tcEnv clsEnv $
                            ContextType NoSpanInfo cx inst
      ocls = getOrigName m cls tcEnv
      ps' = Set.fromList [ Pred scls ty | scls <- superClasses ocls clsEnv ]
      doc = ppPred m $ Pred cls ty
      what = "instance declaration"
  (ps'', _) <- reducePredSet False inst what doc clsEnv ps'
  Set.mapM_ (report . errMissingInstance m inst what doc) $
    ps'' `Set.difference` maxPredSet clsEnv ps
checkInstance _ _ _ = ok

-- All types specified in the optional default declaration of a module
-- must be instances of the Num class. Since these types are used to resolve
-- ambiguous type variables, the predicate sets of the respective instances
-- must be empty.

checkDefault :: TCEnv -> ClassEnv -> Decl a -> INCM ()
checkDefault tcEnv clsEnv (DefaultDecl _ tys) =
  mapM_ (checkDefaultType tcEnv clsEnv) tys
checkDefault _ _ _ = ok

checkDefaultType :: TCEnv -> ClassEnv -> TypeExpr -> INCM ()
checkDefaultType tcEnv clsEnv ty = do
  m <- getModuleIdent
  let TypeContext _ ty' = expandPolyType m tcEnv clsEnv $
                            ContextType NoSpanInfo [] ty
  (ps, _) <- reducePredSet False ty what empty clsEnv
    (Set.singleton $ Pred qNumId ty')
  Set.mapM_ (report . errMissingInstance m ty what empty) ps
  where what = "default declaration"

-- The function 'reducePredSet' simplifies a predicate set of the form
-- (C_1 tau_1,..,C_n tau_n) where the tau_i are arbitrary types into a
-- predicate set where all predicates are of the form C u with u being
-- a type variable. An error is reported if the predicate set cannot
-- be transformed into this form. In addition, we remove all predicates
-- that are implied by others within the same set.
-- When the flag is set, all missing Data preds are ignored

reducePredSet :: HasSpanInfo s => Bool -> s -> String -> Doc -> ClassEnv -> PredSet
              -> INCM (PredSet, PredSet)
reducePredSet b p what doc clsEnv ps = do
  m <- getModuleIdent
  inEnv <- getInstEnv
  let (ps1, ps2) = partitionPredSet $ minPredSet clsEnv $ reducePreds inEnv ps
      ps2' = if b then Set.filter (isNotDataPred m) ps2 else ps2
  Set.mapM_ (reportMissing m) ps2' >> return (ps1, ps2)
  where
    isNotDataPred _ (Pred qid _) = qid /= qDataId
    reportMissing m pr@(Pred _ _) =
      report $ errMissingInstance m p what doc pr
    reducePreds inEnv = Set.concatMap $ reducePred inEnv
    reducePred inEnv predicate = maybe (Set.singleton predicate)
                                       (reducePreds inEnv)
                                       (instPredSet inEnv predicate)

instPredSet :: InstEnv -> Pred -> Maybe PredSet
instPredSet inEnv (Pred qcls ty) =
  case unapplyType False ty of
    (TypeConstructor tc, tys) ->
      fmap (expandAliasType tys . snd3) (lookupInstInfo (qcls, tc) inEnv)
    _ -> Nothing

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

genInstIdents :: ModuleIdent -> TCEnv -> Decl a -> [InstIdent]
genInstIdents m tcEnv (DataDecl    _ tc _ _ qclss) =
  map (flip (genInstIdent m tcEnv) $ ConstructorType NoSpanInfo $ qualify tc)
      qclss
genInstIdents m tcEnv (NewtypeDecl _ tc _ _ qclss) =
  map (flip (genInstIdent m tcEnv) $ ConstructorType NoSpanInfo $ qualify tc)
      qclss
genInstIdents m tcEnv (InstanceDecl _ _ _ qcls ty _) =
  [genInstIdent m tcEnv qcls ty]
genInstIdents _ _     _                            = []

genInstIdent :: ModuleIdent -> TCEnv -> QualIdent -> TypeExpr -> InstIdent
genInstIdent m tcEnv qcls = qualInstIdent m tcEnv . (,) qcls . typeConstr

-- When qualifiying an instance identifier, we replace both the class and
-- type constructor with their original names as found in the type constructor
-- environment.

qualInstIdent :: ModuleIdent -> TCEnv -> InstIdent -> InstIdent
qualInstIdent m tcEnv (cls, tc) = (qual cls, qual tc)
  where
    qual = flip (getOrigName m) tcEnv

unqualInstIdent :: TCEnv -> InstIdent -> InstIdent
unqualInstIdent tcEnv (qcls, tc) = (unqual qcls, unqual tc)
  where
    unqual = head . flip reverseLookupByOrigName tcEnv

isFunType :: Type -> Bool
isFunType (TypeArrow         _ _) = True
isFunType (TypeApply       t1 t2) = isFunType t1 || isFunType t2
isFunType (TypeForall      _  ty) = isFunType ty
isFunType (TypeContext      _ ty) = isFunType ty
isFunType (TypeConstructor     _) = False
isFunType (TypeVariable        _) = False
isFunType (TypeConstrained tys _) = any isFunType tys

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errMultipleInstances :: TCEnv -> [InstSource] -> Message
errMultipleInstances tcEnv iss = message $
  text "Multiple instances for the same class and type" $+$
    nest 2 (vcat (map ppInstSource iss))
  where
    ppInstSource (InstSource i m) = ppInstIdent (unqualInstIdent tcEnv i) <+>
      parens (text "defined in" <+> ppMIdent m)

errMissingInstance :: HasSpanInfo s => ModuleIdent -> s -> String -> Doc -> Pred
                   -> Message
errMissingInstance m p what doc predicate = spanInfoMessage (getSpanInfo p) $ vcat
  [ text "Missing instance for" <+> ppPred m predicate
  , text "in" <+> text what <+> doc
  ]
