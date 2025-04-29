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
   instance environment. It is also checked that there are no duplicate
   instances and that all types specified in a default declaration are
   instances of the Num class.
-}
module Curry.Frontend.Checks.InstanceCheck (instanceCheck) where

import           Control.Monad.Extra        ( concatMapM, unless, unlessM
                                            , when, void, whileM )
import qualified Control.Monad.State as S   (State, execState, gets, modify)
import           Data.Either                (isRight, lefts)
import           Data.List                  ( (\\), nub, partition, sortBy
                                            , tails )
import qualified Data.Map            as Map ( Map, elems, keysSet, restrictKeys
                                            , singleton, toList, unions )
import qualified Data.Set            as Set (fromList, toList)
import           Data.Maybe                 (isJust)

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Base.Position (HasPosition (..))
import Curry.Base.SpanInfo
import Curry.Syntax hiding (impls)
import Curry.Syntax.Pretty

import Curry.Frontend.Base.Expr (fv)
import Curry.Frontend.Base.Messages (Message, spanInfoMessage, internalError)
import Curry.Frontend.Base.SCC (scc)
import Curry.Frontend.Base.TypeExpansion
import Curry.Frontend.Base.Types
import Curry.Frontend.Base.TypeSubst
import Curry.Frontend.Base.Utils (findMultiples)

import Curry.Frontend.Env.Class
import Curry.Frontend.Env.Instance
import Curry.Frontend.Env.TypeConstructor
import Data.List.NonEmpty (NonEmpty (..))

instanceCheck :: [KnownExtension] -> ModuleIdent -> TCEnv -> ClassEnv -> InstEnv -> [Decl a]
              -> (InstEnv, [Message])
instanceCheck exts m tcEnv clsEnv inEnv ds =
  case multipleErrs ++ funDepConflictErrs of
    []   -> execINCM (checkDecls tcEnv clsEnv ds) state
    errs -> (inEnv, errs)
  where
    localInsts = concatMap (genInstSources m tcEnv) ds
    importedISs = concatMap (\(qi, mp) -> map (\(tys, _) -> InstSource NoSpanInfo (qi, tys) m) $ Map.toList mp) $ Map.toList inEnv
    multipleErrs = map (errMultipleInstances tcEnv) $ findMultiples $ localInsts ++ importedISs
    funDepConflictErrs = map (errFunDepConflict tcEnv) $
                           findFunDepConflicts m clsEnv inEnv localInsts
    state = INCState m inEnv exts []

-- In order to provide better error messages, we use the following data type
-- to keep track of an instance's source, i.e., the span and module where it was defined.

data InstSource = InstSource SpanInfo InstIdent ModuleIdent

instance HasPosition InstSource where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasSpanInfo InstSource where
  getSpanInfo (InstSource spi _ _) = spi
  setSpanInfo spi (InstSource _ i m) = InstSource spi i m

instance Eq InstSource where
  InstSource _ i1 _ == InstSource _ i2 _ = i1 == i2

findFunDepConflicts :: ModuleIdent -> ClassEnv -> InstEnv -> [InstSource]
                    -> [(InstSource, InstSource)]
findFunDepConflicts m clsEnv inEnv localInsts =
  [ (InstSource spi1 (cls, itys1) m1, InstSource spi2 (cls, itys2) m2)
  | let inEnv' = foldr (\(InstSource spi i _) -> bindInstInfo i (spi, m, [], [])) inEnv localInsts
  , (cls, instMap) <- Map.toList inEnv'
  , funDep <- classFunDeps cls clsEnv
  , (itys1, (spi1, m1, _, _)) : remInsts <- tails (Map.toList instMap)
  , (itys2, (spi2, m2, _, _)) <- remInsts
  , m1 /= m2 || m1 == m
  , let (lhs1, rhs1) = (getFunDepLhs funDep itys1, getFunDepRhs funDep itys1)
        maxIdLhs1 = maximum (-1 : typeVars lhs1) + 1
        itys2' = expandAliasType (map TypeVariable [maxIdLhs1 ..]) itys2
        (lhs2, rhs2) = (getFunDepLhs funDep itys2', getFunDepRhs funDep itys2')
  , Just sigma <- [unifyTypeLists lhs1 lhs2]
  , subst sigma rhs1 /= subst sigma rhs2
  ]

unifyTypeLists :: [Type] -> [Type] -> Maybe TypeSubst
unifyTypeLists []           []           = Just idSubst
unifyTypeLists (ty1 : tys1) (ty2 : tys2) = do
  sigma1 <- unifyTypeLists tys1 tys2
  sigma2 <- unifyTypes (subst sigma1 ty1) (subst sigma1 ty2)
  return $ sigma2 `compose` sigma1
unifyTypeLists _            _            = Nothing

unifyTypes :: Type -> Type -> Maybe TypeSubst
unifyTypes (TypeVariable tv1) (TypeVariable tv2)
  | tv1 == tv2            = Just idSubst
  | otherwise             = Just (singleSubst tv1 (TypeVariable tv2))
unifyTypes (TypeVariable tv) ty
  | tv `elem` typeVars ty = Nothing
  | otherwise             = Just (singleSubst tv ty)
unifyTypes ty (TypeVariable tv)
  | tv `elem` typeVars ty = Nothing
  | otherwise             = Just (singleSubst tv ty)
unifyTypes (TypeConstructor tc1) (TypeConstructor tc2)
  | tc1 == tc2 = Just idSubst
unifyTypes (TypeApply ty11 ty12) (TypeApply ty21 ty22) =
  unifyTypeLists [ty11, ty12] [ty21, ty22]
unifyTypes ty1@(TypeApply _ _) (TypeArrow ty21 ty22) =
  unifyTypes ty1 (TypeApply (TypeApply (TypeConstructor qArrowId) ty21) ty22)
unifyTypes (TypeArrow ty11 ty12) ty2@(TypeApply _ _) =
  unifyTypes (TypeApply (TypeApply (TypeConstructor qArrowId) ty11) ty12) ty2
unifyTypes (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
  unifyTypeLists [ty11, ty12] [ty21, ty22]
unifyTypes _ _ = Nothing

-- |Instance Check Monad
type INCM = S.State INCState

-- |Internal state of the Instance Check
data INCState = INCState
  { moduleIdent :: ModuleIdent
  , instEnv     :: InstEnv
  , extensions  :: [KnownExtension]
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

hasExtension :: KnownExtension -> INCM Bool
hasExtension ext = S.gets $ elem ext . extensions

report :: Message -> INCM ()
report err = S.modify (\s -> s { errors = err : errors s })

ok :: INCM ()
ok = return ()

checkDecls :: TCEnv -> ClassEnv -> [Decl a] -> INCM ()
checkDecls tcEnv clsEnv ds = do
  mapM_ (bindInstance tcEnv clsEnv) ids
  unlessM (hasExtension NoDataDeriving) $
    mapM (declDeriveDataInfo tcEnv clsEnv) (filter isDataDecl tds) >>=
      mapM_ (bindDerivedInstances clsEnv) . groupDeriveInfos
  mapM (declDeriveInfo tcEnv clsEnv) (filter hasDerivedInstances tds) >>=
    mapM_ (bindDerivedInstances clsEnv) . groupDeriveInfos
  mapM_ (checkInstance tcEnv clsEnv) ids
  mapM_ (checkDefault tcEnv clsEnv) dds
  where (tds, ods) = partition isTypeDecl ds
        ids = filter isInstanceDecl ods
        dds = filter isDefaultDecl ods
        isDataDecl DataDecl {}    = True
        isDataDecl NewtypeDecl {} = True
        isDataDecl _              = False

-- First, the compiler adds all explicit instance declarations to the
-- instance environment.

bindInstance :: TCEnv -> ClassEnv -> Decl a -> INCM ()
bindInstance tcEnv clsEnv (InstanceDecl p _ cx qcls inst ds) = do
  m <- getModuleIdent
  -- Before instances are entered into the instance environment, the context and
  -- instance types have to be expanded and normalized, as they could contain
  -- type synonyms. To report violations of the rules ensuring instance
  -- resolution termination with constraints and instance heads that are as
  -- close to the original code as possible, the type constructors occurring in
  -- them are unqualified. Additionally, the context and instance types are
  -- passed on before normalization, so that the original type variables can be
  -- used (otherwise, these type variables might not be in the correct order
  -- because of type synonyms).
  let PredTypes pls tys = expandPredTypes m tcEnv clsEnv $
                            toPredTypes [] OPred cx inst
      opls = map (\(Pred _ pcls ptys) -> uncurry (Pred OPred) $
                      unqualInstIdent tcEnv (pcls, ptys)) pls
      otys = map (unqualType tcEnv) tys
      PredTypes ipls itys = normalize 0 $ PredTypes pls tys
  term <- checkInstanceTermination m False (nub $ fv (inst, cx)) p opls qcls otys
  fdCov <- checkFunDepCoverage clsEnv p qcls (getOrigName m qcls tcEnv) inst
  when fdCov $ modifyInstEnv $
    bindInstInfo (getOrigName m qcls tcEnv, itys)
                    (p, m, if term then ipls else [], impls [] ds)
  where impls is [] = is
        impls is (FunctionDecl _ _ f (eq:_):ds')
          | f' `elem` map fst is = impls is ds'
          | otherwise            = impls ((f', eqnArity eq) : is) ds'
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

data DeriveInfo = DeriveInfo SpanInfo PredType [Type] [QualIdent]

declDeriveInfo :: TCEnv -> ClassEnv -> Decl a -> INCM DeriveInfo
declDeriveInfo tcEnv clsEnv (DataDecl p tc tvs cs clss) =
  mkDeriveInfo tcEnv clsEnv p tc tvs (concat tyss) clss
  where tyss = map constrDeclTypes cs
declDeriveInfo tcEnv clsEnv (NewtypeDecl p tc tvs nc clss) =
  mkDeriveInfo tcEnv clsEnv p tc tvs [nconstrType nc] clss
declDeriveInfo _ _ _ =
  internalError "InstanceCheck.declDeriveInfo: no data or newtype declaration"

declDeriveDataInfo :: TCEnv -> ClassEnv -> Decl a -> INCM DeriveInfo
declDeriveDataInfo tcEnv clsEnv (DataDecl p tc tvs cs _) =
  mkDeriveDataInfo tcEnv clsEnv p tc tvs (concat tyss)
  where tyss = map constrDeclTypes cs
declDeriveDataInfo tcEnv clsEnv (NewtypeDecl p tc tvs nc _) =
  mkDeriveDataInfo tcEnv clsEnv p tc tvs [nconstrType nc]
declDeriveDataInfo _ _ _ = internalError
  "InstanceCheck.declDeriveDataInfo: no data or newtype declaration"

constrDeclTypes :: ConstrDecl -> [TypeExpr]
constrDeclTypes (ConstrDecl     _ _ tys) = tys
constrDeclTypes (ConOpDecl  _ ty1 _ ty2) = [ty1, ty2]
constrDeclTypes (RecordDecl      _ _ fs) = tys
  where tys = [ty | FieldDecl _ ls ty <- fs, _ <- ls]

mkDeriveInfo :: TCEnv -> ClassEnv -> SpanInfo -> Ident -> [Ident]
             -> [TypeExpr] -> [QualIdent] -> INCM DeriveInfo
mkDeriveInfo tcEnv clsEnv spi tc tvs tys clss = do
  m <- getModuleIdent
  let otc = qualifyWith m tc
      oclss = map (flip (getOrigName m) tcEnv) clss
      PredType ps ty = expandConstrType m tcEnv clsEnv otc tvs tys
      (tys', ty') = arrowUnapply ty
  return $ DeriveInfo spi (PredType ps ty') tys' $ sortClasses clsEnv oclss

mkDeriveDataInfo :: TCEnv -> ClassEnv -> SpanInfo -> Ident -> [Ident]
                 -> [TypeExpr] -> INCM DeriveInfo
mkDeriveDataInfo tcEnv clsEnv spi tc tvs tys = do
  m <- getModuleIdent
  let otc = qualifyWith m tc
      PredType ps ty = expandConstrType m tcEnv clsEnv otc tvs tys
      (tys', ty') = arrowUnapply ty
  return $ DeriveInfo spi (PredType ps ty') tys' [qDataId]

sortClasses :: ClassEnv -> [QualIdent] -> [QualIdent]
sortClasses clsEnv clss = map fst $ sortBy compareDepth $ map adjoinDepth clss
  where (_, d1) `compareDepth` (_, d2) = d1 `compare` d2
        adjoinDepth cls = (cls, length $ allSuperClasses cls clsEnv)

groupDeriveInfos :: [DeriveInfo] -> [[DeriveInfo]]
groupDeriveInfos = scc bound free
  where bound (DeriveInfo _ (PredType _ ty) _ _) = typeConstrs ty
        free (DeriveInfo _ _ tys _) = concatMap typeConstrs tys

bindDerivedInstances :: ClassEnv -> [DeriveInfo] -> INCM ()
bindDerivedInstances clsEnv dis = unless (any hasDataFunType dis) $ do
  mapM_ (enterInitialPredList clsEnv) dis
  whileM $ concatMapM (inferPredLists clsEnv) dis >>= updatePredLists
  where
    hasDataFunType (DeriveInfo _ _ tys clss) =
      clss == [qDataId] && any isFunType tys

enterInitialPredList :: ClassEnv -> DeriveInfo -> INCM ()
enterInitialPredList clsEnv (DeriveInfo spi pty _ clss) =
  mapM_ (bindDerivedInstance clsEnv spi pty) clss

-- Note: The methods and arities entered into the instance environment have
-- to match methods and arities of the later generated instance declarations.
-- TODO: Add remark about value environment entry

bindDerivedInstance :: HasSpanInfo s => ClassEnv -> s -> PredType -> QualIdent
                    -> INCM ()
bindDerivedInstance clsEnv p pty cls = do
  m <- getModuleIdent
  (((_, tys), pls), enter) <- inferPredList clsEnv p pty [] cls
  when enter $ modifyInstEnv (bindInstInfo (cls, tys) (getSpanInfo p, m, pls, impls))
               -- taken from Leif-Erik Krueger
               >> checkMissingImplementations clsEnv p cls tys (map fst impls)
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

inferPredLists :: ClassEnv -> DeriveInfo -> INCM [((InstIdent, PredList), Bool)]
inferPredLists clsEnv (DeriveInfo spi pty@(PredType _ inst) tys clss) = do
  inEnv <- getInstEnv
  let clss' = filter (\cls -> isJust $ lookupInstExact (cls, [inst]) inEnv) clss
  mapM (inferPredList clsEnv spi pty tys) clss'

-- inspired by Leif-Erik Krueger
inferPredList :: HasSpanInfo s => ClassEnv -> s -> PredType -> [Type]
              -> QualIdent -> INCM ((InstIdent, PredList), Bool)
inferPredList clsEnv p (PredType pls inst) tys cls = do
  m <- getModuleIdent
  let doc = ppPred m $ Pred OPred cls [inst]
      pls'   = [Pred OPred cls [ty] | ty <- tys]
      -- taken from Leif-Erik Krueger
      pls''  = expandAliasType [inst] (superClasses cls clsEnv)
      pls''' = plUnions [pls, pls',  pls'']
  (pls4, novarpls) <-
    reducePredList (Derive $ cls == qDataId) p doc clsEnv pls'''
  if cls == qDataId && (not (null novarpls) || any noPolyPred pls4)
    then return    (((cls, [inst]), pls4), False)
    else do term <- checkInstanceTermination m True [] p pls4 cls [inst]
            return (((cls, [inst]), if term then pls4 else []), True)
  where
    noPolyPred (Pred _ _ tys') = not (all isTypeVariable tys')

updatePredLists :: [((InstIdent, PredList), Bool)] -> INCM Bool
updatePredLists = fmap or . mapM (uncurry updatePredList)

updatePredList :: (InstIdent, PredList) -> Bool -> INCM Bool
updatePredList (i, pls) enter = do
  inEnv <- getInstEnv
  case lookupInstExact i inEnv of
    Just (spi, m, pls', is)
      | not enter   -> modifyInstEnv (removeInstInfo i) >> return False
      -- TODO : is this correct every time? Order of elements in list?
      | pls == pls' -> return False
      | otherwise   -> do
        modifyInstEnv $ bindInstInfo i (spi, m, pls, is)
        return True
    _ -> internalError "InstanceCheck.updatePredList"

-- Checks if the instance given by its span info, context, class identifier and
-- instance types follows the instance termination rules.
-- Additionally, this function takes the ident of the current module, a flag
-- signalizing whether the instance is derived and a list of the type variables
-- of the original instance, which is allowed to be empty.
checkInstanceTermination :: HasSpanInfo p => ModuleIdent -> Bool -> [Ident]
                         -> p -> PredList -> QualIdent -> [Type] -> INCM Bool
checkInstanceTermination m d oVars spi pls qcls iTys =
  and <$> mapM checkInstanceTerminationPred pls
 where
  iVars  = typeVars iTys
  iSize  = sum (map typeSize iTys)
  oVars' = oVars ++ identSupply
  iDoc   = pPrint (fromQualPred m oVars' (Pred OPred qcls iTys))

  -- Checks if a constraint of the instance context follows the Paterson
  -- conditions. Only the first two of the three Paterson conditions are tested
  -- since Curry does not yet support type functions (like type families).
  checkInstanceTerminationPred :: Pred -> INCM Bool
  checkInstanceTerminationPred pr@(Pred _ _ pTys) = do
    paterson1 <- checkTypeVarQuantity (typeVars pTys)
    paterson2 <- checkConstraintSize
    return $ paterson1 && paterson2
   where
    cDoc = pPrint $ fromQualPred m oVars' pr

    -- Checks if all type variables in the constraint occur at least as often
    -- in the instance head (the first Paterson condition).
    checkTypeVarQuantity :: [Int] -> INCM Bool
    checkTypeVarQuantity cVars = do
      let errVars = map (oVars' !!) (nub (cVars \\ iVars))
      mapM_ (report . errVarQuantityConstraint d spi cDoc iDoc) errVars
      return $ null errVars

    -- Checks if the constraint is smaller than the instance head (the second
    -- Paterson condition).
    checkConstraintSize :: INCM Bool
    checkConstraintSize =
      if sum (map typeSize pTys) >= iSize
        then report (errNonDecreasingConstraint d spi cDoc iDoc) >> return False
        else return True

-- Returns the size of the given type.
-- The size of a type is the number of all data type constructors and type
-- variables (counting repititions) taken together.
typeSize :: Type -> Int
typeSize (TypeConstructor   _) = 1
typeSize (TypeVariable      _) = 1
typeSize (TypeConstrained _ _) = 1
typeSize (TypeApply   ty1 ty2) = typeSize ty1 + typeSize ty2
typeSize (TypeArrow   ty1 ty2) = 1 + typeSize ty1 + typeSize ty2
typeSize (TypeForall     _ ty) = typeSize ty

checkFunDepCoverage :: HasSpanInfo p => ClassEnv -> p -> QualIdent -> QualIdent
                                     -> [InstanceType] -> INCM Bool
checkFunDepCoverage clsEnv p cls qcls itys =
  let coverageErrors =
        [ errFunDepCoverage p cls itys lhs rhs uncoveredVs
        | funDep <- classFunDeps qcls clsEnv
        , let (lhs, rhs) = (getFunDepLhs funDep itys, getFunDepRhs funDep itys)
              uncoveredVs = nub (fv rhs) \\ fv lhs
        , not (null uncoveredVs)
        ]
  in mapM_ report coverageErrors >> return (null coverageErrors)

-- Then, the compiler checks the contexts of all explicit instance declarations
-- to detect missing super class instances. For a class declaration
--
-- class (D_1, ..., D_k) => C a_1 ... a_n where ...
--
-- where C is a class, a_1 ... a_n are type variables and D_1 ... D_k are super
-- class constraints,
--
-- a super class constraint of C
--
-- D a_{j_1} ... a_{j_l}
--
-- where D is a class and j_1 ... j_l are elements of {1, ..., n},
--
-- and an instance declaration
--
-- instance cx => C T_1 ... T_n where ...
--
-- where cx is the instance context and T_1 ... T_n are type expressions of the
-- form T u_1 ... u_m with T being a type constructor and u_1 ... u_m being type
-- variables
--
-- the compiler ensures that the types T_{j_1} ... T_{j_l} are an instance of D
-- and that the context of the corresponding instance declaration is satisfied
-- by cx.

-- inspired by Leif-Erik Krueger
checkInstance :: TCEnv -> ClassEnv -> Decl a -> INCM ()
checkInstance tcEnv clsEnv (InstanceDecl p _ cx cls inst ds) = do
  m <- getModuleIdent
  let PredTypes pls tys = expandInst m tcEnv clsEnv cx inst
      ocls = getOrigName m cls tcEnv
      -- taken from Leif-Erik Krueger
      pls' = expandAliasType tys (superClasses ocls clsEnv)
      doc = ppPred m $ Pred OPred cls tys
  -- TODO: Is there a better span for these, for example by combining the 'cls'
  --         and 'inst' spans?
  _ <- reducePredList (SuperClass $ maxPredList clsEnv pls) p doc clsEnv pls'
  checkMissingImplementations clsEnv p ocls tys (concatMap impls ds)
 where
  impls (FunctionDecl _ _ f _) = [unRenameIdent f]
  impls _                      = []
checkInstance _ _ _ = ok

-- Taken from Leif-Erik Krueger
-- Next, we report cases where an overlapping instance error would occur in the
-- dictionary translation because of a missing method implementation. For
-- example, if an instance for Eq String only implementing (==) was added, then
-- there would be multiple possible implementations of (/=): The default
-- implementation of (/=) uses (==) and both the added instance for Eq String
-- and the predefined instance for Eq [a] would provide a fitting implementation
-- of (==). To prevent such ambiguities, we must ensure that an instance, which
-- is completely overlapped by another instance (so the latter instance always
-- matches when the former one does), implements every class method.

-- taken from Leif-Erik Krueger
checkMissingImplementations :: HasSpanInfo p => ClassEnv -> p -> QualIdent
                            -> [Type] -> [Ident] -> INCM ()
checkMissingImplementations clsEnv p qcls tys impls = do
  m <- getModuleIdent
  inEnv <- getInstEnv
  let missingImpls = classMethods qcls clsEnv \\ impls
      miDoc = nest 2 $ list (map ppIdent missingImpls)
      miError = instPredList MissingImpls m p miDoc (Pred OPred qcls tys) inEnv
  unless (null missingImpls || isRight miError) $ mapM_ report (lefts [miError])




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
  let PredType _ ty' = expandPolyType OPred m tcEnv clsEnv $
                         QualTypeExpr NoSpanInfo [] ty
 -- taken from Leif-Erik Krueger
  void $ reducePredList Default ty empty clsEnv [Pred OPred qNumId [ty']]

-- The function 'reducePredSet' simplifies a predicate set of the form
-- (C_1 tau_{1,1} ... tau_{1,n_1}, ..., C_m tau_{m,1} ... tau_{m,n_m}) where the
-- tau_{i,j} are arbitrary types into a predicate set where all predicates are
-- of the form C u_1 ... u_n with the u_i being type variables.
-- An error is reported if the predicate set cannot be transformed into this
-- form. In addition, we remove all predicates that are implied by others
-- within the same set.
-- When the flag is set, all missing Data preds are ignored.

-- The following is taken from Leif-Erik Krueger
-- The specifics of this reduction and how predicates remaining after the
-- reduction are treated, depends on an 'ReductionMode' argument. The following
-- modes are used in the instance check:

-- * 'Derive' is used when inferring predicate sets of derived instances. In
--   this mode, we also consider overlap between unifiable instances (see the
--   instance environment for information about matching and unifiable
--   instances), which matches the behaviour of the GHC. After the reduction, we
--   report every remaining predicate which is not of the form C a_1 ... a_n
--   with C being a class and a_1 ... a_n being type variables. An exception to
--   this is made for derived instances for the Data class, which are marked by
--   a flag included in this mode: Since these are derived automatically, we do
--   not report remaining Data predicates for them, but instead remove the
--   instance from the environment if there are remaining predicates that do not
--   match the required form (see 'inferPredSet' and 'updatePredSet').

-- * 'SuperClass' is used when determining missing super class instances. If a
--   predicate found within the set given with this mode, which represents the
--   instance context, occurs during the reduction, it is directly removed. We
--   can therefore simply report all predicates remaining after the reduction,
--   as they belong to missing super class instances or unsatisfied constraints
--   of existing super class instances.

-- * 'Default' is used when checking whether a type given in a default
--   declaration is an instance of the Num class. All predicates remaining after
--   the reduction are reported.

-- * 'MissingImpls' is used to determine whether an instance is completely
--   overlapped by another instance to prevent errors arising from missing
--   method implementations (see 'checkMissingImplementations'). This mode is
--   not used with 'reducePredSet', but only with its helper function
--   'instPredSet'.

-- taken from Leif-Erik Krueger
data ReductionMode = Derive Bool | SuperClass [Pred] | Default | MissingImpls
  deriving Eq


reducePredList :: HasSpanInfo s => ReductionMode -> s -> Doc -> ClassEnv -> PredList
              -> INCM (PredList, PredList)
reducePredList rm p doc clsEnv pls = do
  m <- getModuleIdent
  inEnv <- getInstEnv
  -- taken from Leif-Erik Krueger
  let pm = reducePreds m inEnv pls
      pls' = minPredList clsEnv (Set.toList $ Map.keysSet pm)
      (pls1,pls2) = partitionPredList pls'
      plsNoPoly = pls2 `plUnion` filter noPolyPred pls1
      plsReport = case rm of Derive True  -> filter isNotDataPred plsNoPoly
                             Derive False -> plsNoPoly
                             _            -> pls'
  mapM_ report (Map.elems (Map.restrictKeys pm (Set.fromList plsReport)))
  return (pls1, pls2)
  where
    noPolyPred (Pred _ _ tys') = not (all isTypeVariable tys')
    isNotDataPred (Pred _ qid _) = qid /= qDataId
    -- taken from Leif-Erik Krueger
    reducePreds :: ModuleIdent -> InstEnv -> [Pred] -> Map.Map Pred Message
    reducePreds m inEnv = Map.unions . map (reducePred m inEnv)

    -- taken from Leif-Erik Krueger
    reducePred :: ModuleIdent -> InstEnv -> Pred -> Map.Map Pred Message
    reducePred m inEnv predicate =
      either (Map.singleton predicate) (reducePreds m inEnv)
        (instPredList rm m p doc predicate inEnv)

-- taken from Leif-Erik Krueger
instPredList :: HasSpanInfo p => ReductionMode -> ModuleIdent -> p -> Doc -> Pred
             -> InstEnv -> Either Message PredList
instPredList rm m p doc pr@(Pred _ qcls tys) inEnv =
  if pr `plElem` getGivenPreds rm
  then Right []
  else case lookupInstMatch qcls tys inEnv of
         ([],_) -> Left $ errMissingInstance rm m p doc pr
         ([(_, _, pls, _, _, sigma)], insts) ->
             if isDeriveMode rm && length insts > 1
             then Left $ errInstanceOverlap rm True m p doc pr insts
             else Right $ subst sigma pls
         (insts, _) -> Left $ errInstanceOverlap rm False m p doc pr insts

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

genInstSources :: ModuleIdent -> TCEnv -> Decl a -> [InstSource]
genInstSources m tcEnv decl = flip (InstSource spi) m <$> iis
  where iis = genInstIdents m tcEnv decl
        spi = getSpanInfo decl

genInstIdents :: ModuleIdent -> TCEnv -> Decl a -> [InstIdent]
genInstIdents m tcEnv (DataDecl    _ tc _ _ qclss) =
  map (flip (genInstIdent m tcEnv) [ConstructorType NoSpanInfo $ qualify tc])
      qclss
genInstIdents m tcEnv (NewtypeDecl _ tc _ _ qclss) =
  map (flip (genInstIdent m tcEnv) [ConstructorType NoSpanInfo $ qualify tc])
      qclss
genInstIdents m tcEnv (InstanceDecl _ _ _ qcls tys _) =
  [genInstIdent m tcEnv qcls tys]
genInstIdents _ _     _                            = []

genInstIdent :: ModuleIdent -> TCEnv -> QualIdent -> [TypeExpr] -> InstIdent
genInstIdent m tcEnv qcls tys =
  (getOrigName m qcls tcEnv, map (expandType m tcEnv) (toTypes [] tys))

-- While the qualification of instance idents does not need its own function, as
-- the replacement of the type constructors in the instance types with their
-- original names is done by 'expandType' already, an unqualification function
-- is needed to display instances without unnecessary module identifiers in
-- error messages. This unqualification is done by doing a reverse lookup with
-- the original name in the type constructor environment.

unqualInstIdent :: TCEnv -> InstIdent -> InstIdent
unqualInstIdent tcEnv (qcls, tys) =
  (unqualTC tcEnv qcls, map (unqualType tcEnv) tys)

unqualType :: TCEnv -> Type -> Type
unqualType tcEnv (TypeConstructor     tc) = TypeConstructor (unqualTC tcEnv tc)
unqualType tcEnv (TypeApply      ty1 ty2) =
  TypeApply (unqualType tcEnv ty1) (unqualType tcEnv ty2)
unqualType _     tv@(TypeVariable      _) = tv
unqualType tcEnv (TypeConstrained tys tv) =
  TypeConstrained (map (unqualType tcEnv) tys) tv
unqualType tcEnv (TypeArrow      ty1 ty2) =
  TypeArrow (unqualType tcEnv ty1) (unqualType tcEnv ty2)
unqualType tcEnv (TypeForall      tvs ty) = TypeForall tvs (unqualType tcEnv ty)

-- TODO: With FlexibleInstances, where some types after expansion might not
--         be in scope, is using 'head' safe or should the given name be
--         returned as a default option?
-- taken from Leif-Erik Krueger
unqualTC :: TCEnv -> QualIdent -> QualIdent
unqualTC tcEnv otc = case reverseLookupByOrigName otc tcEnv of
   []   -> otc
   tc:_ -> tc

isFunType :: Type -> Bool
isFunType (TypeArrow         _ _) = True
isFunType (TypeApply       t1 t2) = isFunType t1 || isFunType t2
isFunType (TypeForall      _  ty) = isFunType ty
isFunType (TypeConstrained tys _) = any isFunType tys
isFunType _                       = False

-- taken from Leif-Erik Krueger
redModeWhatDoc :: ReductionMode -> Doc
redModeWhatDoc (Derive _)     = text "derived instance for"
redModeWhatDoc (SuperClass _) = text "instance declaration for"
redModeWhatDoc Default        = text "default declaration"
redModeWhatDoc MissingImpls   = text "default method implementation(s) for"

-- taken from Leif-Erik Krueger
getGivenPreds :: ReductionMode -> [Pred]
getGivenPreds (SuperClass instcx) = instcx
getGivenPreds _                   = []

-- taken from Leif-Erik Krueger
isDeriveMode :: ReductionMode -> Bool
isDeriveMode (Derive _) = True
isDeriveMode _          = False

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errMultipleInstances :: TCEnv -> NonEmpty InstSource -> Message
errMultipleInstances tcEnv (is@(InstSource spi i _) :| iss) = spanInfoMessage spi $
  text "Multiple instances for the same class" <+> text typeText $+$
    nest 2 (vcat (map (ppInstSource tcEnv) (is:iss)))
  where typeText = case length (snd i) of 0 -> ""
                                          1 -> "and type"
                                          _ -> "and types"

errFunDepConflict :: TCEnv -> (InstSource, InstSource) -> Message
errFunDepConflict tcEnv (is1@(InstSource spi _ _), is2) = spanInfoMessage spi $
  text "Functional dependency conflict between instances" $+$
    nest 2 (vcat (map (ppInstSource tcEnv) [is1, is2]))

ppInstSource :: TCEnv -> InstSource -> Doc
ppInstSource tcEnv (InstSource _ i m) = ppInstIdent (unqualInstIdent tcEnv i) <+>
  parens (text "defined in" <+> ppMIdent m)

-- taken from Leif-Erik Krueger
errMissingInstance :: HasSpanInfo s => ReductionMode -> ModuleIdent -> s -> Doc
                   -> Pred -> Message
errMissingInstance rm m p doc predicate = spanInfoMessage (getSpanInfo p) $ vcat
  [ text "Missing instance for" <+> ppPred m predicate
  , text "in" <+> redModeWhatDoc rm
  , doc
  ]

-- taken from Leif-Erik Krueger
errInstanceOverlap :: HasSpanInfo p => ReductionMode -> Bool -> ModuleIdent -> p
                   -> Doc -> Pred -> [InstMatchInfo] -> Message
errInstanceOverlap rm tvChoice m p doc pr@(Pred _ qcls _) insts =
  spanInfoMessage p $ vcat $
       [ text "Instance overlap for" <+> ppPred m pr
       , text "arising in" <+> redModeWhatDoc rm
       , doc
       , text "Matching instances:"
       , nest 2 $ vcat $ map displayMatchingInst insts
       ] ++ note
 where
  -- TODO: This function is very similar to 'ppInstSource', but the latter
  --         currently needs a 'TCEnv', which would need to be carried around in
  --         many functions to be available here. Check if this extra effort
  --         would produce better error messages.
  displayMatchingInst :: InstMatchInfo -> Doc
  displayMatchingInst (_, m', _, itys, _, _) =
    ppPred m (Pred OPred qcls itys) <+> parens (text "defined in" <+> pPrint m')

  note = map text $ case (rm, tvChoice) of
    (MissingImpls, _) -> [ "(Add implementations for all class methods in"
                         , "an explicit instance declaration to avoid this.)" ]
    (_, True)         -> [ "(The choice depends on the"
                         , "instantiation of type variables.)" ]
    _                 -> []


errVarQuantityConstraint :: HasSpanInfo p => Bool -> p -> Doc -> Doc -> Ident
                                          -> Message
errVarQuantityConstraint d spi cDoc iDoc varId = spanInfoMessage spi $ vcat
  [ text "The type variable" <+> text (escName varId)
    <+> text "occurs more often"
  , text "in the constraint" <+> cDoc
  , endDoc
  ]
 where
  endDoc = if d then text "than in the head of the derived instance" $$ iDoc
                else text "than in the instance head" <+> iDoc

errNonDecreasingConstraint :: HasSpanInfo p => Bool -> p -> Doc -> Doc
                                            -> Message
errNonDecreasingConstraint d spi cDoc iDoc = spanInfoMessage spi $ vcat
  [text "The type constraint" <+> cDoc <+> text "is not smaller", endDoc]
 where
  endDoc = if d then text "than the head of the derived instance" $$ iDoc
                else text "than the instance head" <+> iDoc

errFunDepCoverage :: HasSpanInfo p => p -> QualIdent -> [InstanceType]
                  -> [InstanceType] -> [InstanceType] -> [Ident] -> Message
errFunDepCoverage p cls itys lhs rhs uncoveredVs = spanInfoMessage p $ vcat
  [ text "Violation of a functional dependency in instance declaration for"
  , pPrint (Constraint NoSpanInfo cls itys)
  , text "The left-hand side instance type" <+> lhsDoc1
    <+> hsep (map (pPrintPrec 2) lhs)
  , lhsDoc2 <+> text "not uniquely determine the right-hand side instance type"
    <+> rhsDoc <+> hsep (map (pPrintPrec 2) rhs)
  , text "because the type" <+> varDoc <+> text "not occur in the former."
  ]
 where
  (lhsDoc1, lhsDoc2) = if length lhs == 1 then (text "type", text "does")
                                          else (text "types", text "do")
  rhsDoc = if length rhs == 1 then text "type" else text "types"
  varDoc = case uncoveredVs of
    []  -> text "variables do" -- This case should not be able to occur
    [var] -> text "variable" <+> text (escName var) <+> text "does"
    _   -> text "variables"
           <+> hsep (punctuate comma (map (text . escName) (init uncoveredVs)))
           <+> text "and" <+> text (escName (last uncoveredVs)) <+> text "do"
