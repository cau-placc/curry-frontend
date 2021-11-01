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
module Checks.InstanceCheck (instanceCheck) where

import           Control.Monad.Extra        ( concatMapM, unless, void, when
                                            , whileM )
import qualified Control.Monad.State as S   (State, execState, gets, modify)
import           Data.Either                (isRight, lefts)
import           Data.List                  ((\\), nub, partition, sortBy)
import qualified Data.Map            as Map ( Map, elems, keysSet, restrictKeys
                                            , singleton, unions )
import           Data.Maybe                 (isJust)
import qualified Data.Set.Extra      as Set

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Base.SpanInfo
import Curry.Syntax hiding (impls)
import Curry.Syntax.Pretty

import Base.CurryTypes
import Base.Expr (fv)
import Base.Messages (Message, spanInfoMessage, message, internalError)
import Base.SCC (scc)
import Base.TypeExpansion
import Base.Types
import Base.TypeSubst
import Base.Utils (fst3, findMultiples)

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
    imported = map (uncurry InstSource . fmap fst3) $ instEnvList inEnv
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
bindInstance tcEnv clsEnv (InstanceDecl p _ cx qcls inst ds) = do
  m <- getModuleIdent
  -- Before instances are entered into the instance environment, the context and
  -- instance types have to be expanded and normalized, as they could contain
  -- type synonyms. To report violations of the rules ensuring the termination
  -- of context reduction with constraints and instance heads that are as close
  -- to the original code as possible, the type constructors occurring in them
  -- are unqualified for these checks. Additionally, the context and instance
  -- types are passed on before normalization, so that the original type
  -- variables can be used (otherwise, these type variables might not be in the
  -- correct order because of type synonyms).
  let PredTypes ps tys = expandPredTypes m tcEnv clsEnv $
                           toPredTypes [] OPred cx inst
      uqps = Set.map (\(Pred _ pcls ptys) -> uncurry (Pred OPred) $
                       unqualInstIdent tcEnv (pcls, ptys)) ps
      uqtys = map (unqualType tcEnv) tys
      PredTypes ips itys = normalize 0 $ PredTypes ps tys
  term <- checkInstanceTermination m False (nub $ fv inst) p uqps qcls uqtys
  -- Instances violating the termination rules are entered into the instance
  -- environment with an empty predicate set. This prevents both infinite loops
  -- occurring in the context reduction of the instance check and unnecessary
  -- consequential errors because of missing (super class) instances.
  modifyInstEnv $ bindInstInfo (getOrigName m qcls tcEnv, itys)
                    (m, if term then ips else emptyPredSet, impls [] ds)
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

data DeriveInfo = DeriveInfo SpanInfo PredType [Type] [QualIdent]

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
  mapM_ (enterInitialPredSet clsEnv) dis
  whileM $ concatMapM (inferPredSets clsEnv) dis >>= updatePredSets
  where
    hasDataFunType (DeriveInfo _ _ tys clss) =
      clss == [qDataId] && any isFunType tys

enterInitialPredSet :: ClassEnv -> DeriveInfo -> INCM ()
enterInitialPredSet clsEnv (DeriveInfo spi pty _ clss) =
  mapM_ (bindDerivedInstance clsEnv spi pty) clss

-- Note: The methods and arities entered into the instance environment have
-- to match methods and arities of the later generated instance declarations.
-- TODO: Add remark about value environment entry

bindDerivedInstance :: HasSpanInfo s => ClassEnv -> s -> PredType -> QualIdent
                    -> INCM ()
bindDerivedInstance clsEnv p pty cls = do
  m <- getModuleIdent
  (((_, tys), ps), enter) <- inferPredSet clsEnv p pty [] cls
  when enter $ modifyInstEnv (bindInstInfo (cls, tys) (m, ps, impls))
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

inferPredSets :: ClassEnv -> DeriveInfo -> INCM [((InstIdent, PredSet), Bool)]
inferPredSets clsEnv (DeriveInfo spi pty@(PredType _ inst) tys clss) = do
  inEnv <- getInstEnv
  let clss' = filter (\cls -> isJust $ lookupInstExact (cls, [inst]) inEnv) clss
  mapM (inferPredSet clsEnv spi pty tys) clss'

inferPredSet :: HasSpanInfo s => ClassEnv -> s -> PredType -> [Type]
             -> QualIdent -> INCM ((InstIdent, PredSet), Bool)
inferPredSet clsEnv p (PredType ps inst) tys cls = do
  m <- getModuleIdent
  let doc  = ppPred m $ Pred OPred cls [inst]
      ps'  = Set.fromList [Pred OPred cls [ty] | ty <- tys]
      ps'' = expandAliasType [inst] (superClasses cls clsEnv)
      ps3  = ps `Set.union` ps' `Set.union` ps''
  (ps4, novarps) <- reducePredSet (Derive $ cls == qDataId) p doc clsEnv ps3
  if cls == qDataId && (not (null novarps) || any noPolyPred ps4)
    then return    (((cls, [inst]), ps4), False)
    else do term <- checkInstanceTermination m True [] p ps4 cls [inst]
            return (((cls, [inst]), if term then ps4 else emptyPredSet), True)
 where
  noPolyPred (Pred _ _ tys') = any (not . isTypeVariable) tys'

updatePredSets :: [((InstIdent, PredSet), Bool)] -> INCM Bool
updatePredSets = fmap or . mapM (uncurry updatePredSet)

updatePredSet :: (InstIdent, PredSet) -> Bool -> INCM Bool
updatePredSet (i, ps) enter = do
  inEnv <- getInstEnv
  case lookupInstExact i inEnv of
    Just (m, ps', is)
      | not enter -> modifyInstEnv (removeInstInfo i) >> return False
      | ps == ps' -> return False
      | otherwise -> do
        modifyInstEnv $ bindInstInfo i (m, ps, is)
        return True
    _ -> internalError "InstanceCheck.updatePredSet"

-- Checks if the instance given by its span info, context, class identifier and
-- instance types follows the rules ensuring termination of context reduction.
-- Additionally, this function takes the ident of the current module, a flag
-- signalizing whether the instance is derived and a list of the type variables
-- of the original instance, which is allowed to be empty.
checkInstanceTermination :: HasSpanInfo p => ModuleIdent -> Bool -> [Ident]
                         -> p -> PredSet -> QualIdent -> [Type] -> INCM Bool
checkInstanceTermination m d oVars spi ps qcls iTys =
  and <$> mapM checkInstanceTerminationPred (Set.toList ps)
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

-- Then, the compiler checks the contexts of all explicit instance declarations
-- to detect missing super class instances. For a class declaration
--
-- class (D_1, ..., D_k) => C a_1 ... a_m where ...
--
-- where C is a class, a_1 ... a_m are type variables and D_1 ... D_k are super
-- class constraints, and an instance declaration
--
-- instance cx => C T_1 ... T_m where ...
--
-- where cx is the instance context and T_1 ... T_m are type expressions, the
-- compiler ensures that the predicates sigma(D_1) ... sigma(D_k), where sigma
-- is the substitution {a_1 -> T_1, ..., a_m -> T_m}, are satisfied by cx or the
-- instance environment. This means that each of these predicates must be
-- included in cx or there must exist a single instance declaration matching the
-- predicate whose context is satisfied by cx or the instance environment.

checkInstance :: TCEnv -> ClassEnv -> Decl a -> INCM ()
checkInstance tcEnv clsEnv (InstanceDecl p _ cx cls inst ds) = do
  m <- getModuleIdent
  let PredTypes ps tys = expandInst m tcEnv clsEnv cx inst
      ocls = getOrigName m cls tcEnv
      ps'  = expandAliasType tys (superClasses ocls clsEnv)
      doc  = ppPred m $ Pred OPred cls tys
  _ <- reducePredSet (SuperClass (maxPredSet clsEnv ps)) p doc clsEnv ps'
  checkMissingImplementations clsEnv p ocls tys (concatMap impls ds)
 where
  impls (FunctionDecl _ _ f _) = [unRenameIdent f]
  impls _                      = []
checkInstance _ _ _ = ok

-- Next, we report cases where an overlapping instance error would occur in the
-- dictionary translation because of a missing method implementation. For
-- example, if an instance for Eq String only implementing (==) was added, then
-- there would be multiple possible implementations of (/=): The default
-- implementation of (/=) uses (==) and both the added instance for Eq String
-- and the predefined instance for Eq [a] would provide a fitting implementation
-- of (==). To prevent such ambiguities, we must ensure that an instance, which
-- is completely overlapped by another instance (so the latter instance always
-- matches when the former one does), implements every class method.

checkMissingImplementations :: HasSpanInfo p => ClassEnv -> p -> QualIdent
                            -> [Type] -> [Ident] -> INCM ()
checkMissingImplementations clsEnv p qcls tys impls = do
  m <- getModuleIdent
  inEnv <- getInstEnv
  let missingImpls = classMethods qcls clsEnv \\ impls
      miDoc = nest 2 $ list (map ppIdent missingImpls)
      miError = instPredSet MissingImpls m p miDoc (Pred OPred qcls tys) inEnv
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
  void $ reducePredSet Default ty empty clsEnv $
    (Set.singleton $ Pred OPred qNumId [ty'])

-- The function 'reducePredSet' simplifies a predicate set by recursively
-- replacing individual predicates by the instance context of a matching
-- instance until no further reduction is possible. A predicate is not reduced
-- if there is an instance overlap, i.e. there are multiple matching instances.

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

data ReductionMode = Derive Bool | SuperClass PredSet | Default | MissingImpls
  deriving Eq

reducePredSet :: HasSpanInfo s => ReductionMode -> s -> Doc -> ClassEnv
              -> PredSet -> INCM (PredSet, PredSet)
reducePredSet rm p doc clsEnv ps = do
  m <- getModuleIdent
  inEnv <- getInstEnv
  let pm  = reducePreds m inEnv ps
      ps' = minPredSet clsEnv (Map.keysSet pm)
      (ps1, ps2) = partitionPredSet ps'
      psNoPoly = ps2 `Set.union` Set.filter noPolyPred ps1
      psReport = case rm of Derive True  -> Set.filter isNotDataPred psNoPoly
                            Derive False -> psNoPoly
                            _            -> ps'
  mapM_ report (Map.elems (Map.restrictKeys pm psReport))
  return (ps1, ps2)
 where
  noPolyPred (Pred _ _ tys') = any (not . isTypeVariable) tys'
  isNotDataPred (Pred _ qid _) = qid /= qDataId

  reducePreds :: ModuleIdent -> InstEnv -> PredSet -> Map.Map Pred Message
  reducePreds m inEnv = Map.unions . map (reducePred m inEnv) . Set.toList

  reducePred :: ModuleIdent -> InstEnv -> Pred -> Map.Map Pred Message
  reducePred m inEnv pr = either (Map.singleton pr) (reducePreds m inEnv) $
                            instPredSet rm m p doc pr inEnv

-- Looks up a predicate in the instance environment and the predicates given by
-- the 'ReductionMode' and returns either the corresponding reduced predicate
-- set or an error message explaining why this predicate could not be reduced.
-- Notice that these messages are not reported here, as they simply represent
-- unreducible predicates. Which of these predicates are acceptable depends on
-- the reduction mode and is decided in 'reducePredSet'.
instPredSet :: HasSpanInfo p => ReductionMode -> ModuleIdent -> p -> Doc -> Pred
            -> InstEnv -> Either Message PredSet
instPredSet rm m p doc pr@(Pred _ qcls tys) inEnv =
  if pr `psMember` getGivenPreds rm
    then Right emptyPredSet
    else case lookupInstMatch qcls tys inEnv of
           ([], _) -> Left $ errMissingInstance rm m p doc pr
           ([(_, ps, _, _, sigma)], insts) ->
             if isDeriveMode rm && length insts > 1
               then Left $ errInstanceOverlap rm True m p doc pr insts
               else Right $ subst sigma ps
           (insts, _) -> Left $ errInstanceOverlap rm False m p doc pr insts

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

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
  ( getOrigName m qcls tcEnv
  , normalize 0 (map (expandType m tcEnv) (toTypes [] tys)) )

-- While the qualification of instance idents does not need its own function, as
-- the replacement of the type constructors in the instance types with their
-- original names is done by 'expandType' already, an unqualification function
-- is needed to display instances without unnecessary module identifiers in
-- error messages. This unqualification is done by doing a reverse lookup with
-- the original name in the type constructor environment. Some type constructors
-- might not be in scope after the expansion of type synonyms however, in which
-- case we use the original name of the type constructor.

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

unqualTC :: TCEnv -> QualIdent -> QualIdent
unqualTC tcEnv otc = case reverseLookupByOrigName otc tcEnv of uqtc : _ -> uqtc
                                                               []       -> otc

isFunType :: Type -> Bool
isFunType (TypeArrow         _ _) = True
isFunType (TypeApply       t1 t2) = isFunType t1 || isFunType t2
isFunType (TypeForall      _  ty) = isFunType ty
isFunType (TypeConstrained tys _) = any isFunType tys
isFunType _                       = False

redModeWhatDoc :: ReductionMode -> Doc
redModeWhatDoc (Derive _)     = text "derived instance for"
redModeWhatDoc (SuperClass _) = text "instance declaration for"
redModeWhatDoc Default        = text "default declaration"
redModeWhatDoc MissingImpls   = text "default method implementation(s) for"

getGivenPreds :: ReductionMode -> PredSet
getGivenPreds (SuperClass instcx) = instcx
getGivenPreds _                   = emptyPredSet

isDeriveMode :: ReductionMode -> Bool
isDeriveMode (Derive _) = True
isDeriveMode _          = False

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errMultipleInstances :: TCEnv -> [InstSource] -> Message
errMultipleInstances _     []         = internalError
  "InstanceCheck.errMultipleInstances: Empty instance list"
errMultipleInstances tcEnv iss@(is:_) = message $
  text "Multiple instances for the same class" <+> text typeText $+$
    nest 2 (vcat (map ppInstSource iss))
  where
    ppInstSource (InstSource i m) = ppInstIdent (unqualInstIdent tcEnv i) <+>
      parens (text "defined in" <+> ppMIdent m)
    typeText = case (length . snd . \(InstSource i' _) -> i') is of
                 0 -> ""
                 1 -> "and type"
                 _ -> "and types"

errMissingInstance :: HasSpanInfo s => ReductionMode -> ModuleIdent -> s -> Doc
                   -> Pred -> Message
errMissingInstance rm m p doc predicate = spanInfoMessage (getSpanInfo p) $ vcat
  [ text "Missing instance for" <+> ppPred m predicate
  , text "arising from" <+> redModeWhatDoc rm
  , doc
  ]

-- This error function has an extra flag used to mark an overlap between
-- unifiable instances. If set, a short note explaining the overlap is added to
-- the error message.
errInstanceOverlap :: HasSpanInfo p => ReductionMode -> Bool -> ModuleIdent -> p
                   -> Doc -> Pred -> [InstMatchInfo] -> Message
errInstanceOverlap rm tvChoice m p doc pr@(Pred _ qcls _) insts =
  spanInfoMessage p $ vcat $
    [ text "Instance overlap for" <+> ppPred m pr
    , text "arising from" <+> redModeWhatDoc rm
    , doc
    , text "Matching instances:"
    , nest 2 $ vcat $ map displayMatchingInst insts
    ] ++ note
 where
  -- TODO: Unqualified instances could be displayed here by combining this
  --       function with 'ppInstSource', but this would require adding a 'TCEnv'
  --       to the 'INCState' or as an argument to multiple functions.
  displayMatchingInst :: InstMatchInfo -> Doc
  displayMatchingInst (m', _, itys, _, _) =
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
