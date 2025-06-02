{- |
    Module      :  $Header$
    Description :  Checks for irregular code
    Copyright   :  (c) 2006        Martin Engelke
                       2011 - 2014 Björn Peemöller
                       2014 - 2015 Jan Tikovsky
                       2016 - 2017 Finn Teegen
                       2017 - 2023 Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module searches for potentially irregular code and generates
    warning messages.
-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
module Checks.WarnCheck (warnCheck) where

import           Prelude hiding ((<>))
import           Control.Applicative
  ((<|>))
import           Control.Monad
  (filterM, foldM_, guard, liftM, liftM2, when, unless, void)
import           Control.Monad.State.Strict
  (State, execState, gets, modify, MonadState)
import Control.Monad.Trans.Maybe (MaybeT (..), runMaybeT)
import qualified Data.IntSet         as IntSet
  (IntSet, empty, insert, notMember, singleton, union, unions)
import           Data.Map
  (Map)
import qualified Data.Map            as Map
  (empty, insert, lookup, (!), fromList, union)
import           Data.Maybe
  (catMaybes, fromMaybe, listToMaybe, isJust)
import           Data.List
  ((\\), intersect, intersectBy, nub, sort, unionBy, find)
import           Data.Char
  (isLower, isUpper, toLower, toUpper, isAlpha)
import qualified Data.Set.Extra as Set
import           Data.Tuple.Extra
  (snd3)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Base.SpanInfo
import Curry.Syntax

import Base.Messages   (Message, spanInfoMessage, internalError)
import Base.NestEnv    ( NestEnv, emptyEnv, localNestEnv, nestEnv, unnestEnv
                       , qualBindNestEnv, qualInLocalNestEnv, qualLookupNestEnv
                       , qualModifyNestEnv)
import Base.TopEnv     (allBoundQualIdents)
import Base.Types
import Base.Utils (findMultiples)
import Checks.DeterminismCheck (applyDetType)
import Env.ModuleAlias (AliasEnv)
import Env.Class (ClassEnv, visibleClassMethods, hasDefaultImpl, minPredSet)
import Env.TypeConstructor ( TCEnv, TypeInfo (..), lookupTypeInfo
                           , qualLookupTypeInfo, getOrigName, qualLookupTypeInfoUnique )
import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

import CompilerOpts

-- Find potentially incorrect code in a Curry program and generate warnings
-- for the following issues:
--   - multiply imported modules, multiply imported/hidden values
--   - unreferenced variables
--   - shadowing variables
--   - idle case alternatives
--   - overlapping case alternatives
--   - non-adjacent function rules
--   - wrong case mode
--   - redundant context
--   - determinism of IO actions
warnCheck :: WarnOpts -> CaseMode -> AliasEnv -> ValueEnv -> TCEnv -> ClassEnv
          -> Module (PredType, DetType) -> [Message]
warnCheck wOpts cOpts aEnv valEnv tcEnv clsEnv mdl
  = runOn (initWcState mid aEnv valEnv tcEnv clsEnv (wnWarnFlags wOpts) cOpts ds) $ do
      checkImports is
      checkDeclGroup False (void <$> ds)
      checkExports es
      checkMissingTypeSignatures ds
      checkModuleAlias is
      checkCaseMode ds
      checkRedContext ds
      checkDeterministicIO ds
  where Module _ _ _ mid es is ds = mdl

type ScopeEnv = NestEnv IdInfo

-- Current state of generating warnings
data WcState = WcState
  { moduleId    :: ModuleIdent
  , scope       :: ScopeEnv
  , aliasEnv    :: AliasEnv
  , valueEnv    :: ValueEnv
  , tyConsEnv   :: TCEnv
  , classEnv    :: ClassEnv
  , warnFlags   :: [WarnFlag]
  , caseMode    :: CaseMode
  , warnings    :: [Message]
  , signatures  :: Map Ident DetExpr
  }

-- The monadic representation of the state allows the usage of monadic
-- syntax (do expression) for dealing easier and safer with its
-- contents.
type WCM = State WcState

initWcState :: ModuleIdent -> AliasEnv -> ValueEnv -> TCEnv -> ClassEnv
            -> [WarnFlag] -> CaseMode -> [Decl a] -> WcState
initWcState mid ae ve te ce wf cm ds = WcState mid emptyEnv ae ve te ce wf cm [] $
  Map.fromList $ concat $ [ map (,s) is | DetSig _ is s <- ds ]

getModuleIdent :: MonadState WcState m => m ModuleIdent
getModuleIdent = gets moduleId

getDetSignatures :: WCM (Map Ident DetExpr)
getDetSignatures = gets signatures

modifyScope :: (ScopeEnv -> ScopeEnv) -> WCM ()
modifyScope f = modify $ \s -> s { scope = f $ scope s }

warnsFor :: WarnFlag -> WCM Bool
warnsFor f = gets $ \s -> f `elem` warnFlags s

warnFor :: WarnFlag -> WCM () -> WCM ()
warnFor f act = do
  warn <- warnsFor f
  when warn act

report :: Message -> WCM ()
report w = modify $ \ s -> s { warnings = w : warnings s }

unAlias :: QualIdent -> WCM QualIdent
unAlias q = do
  aEnv <- gets aliasEnv
  case qidModule q of
    Nothing -> return q
    Just m  -> case Map.lookup m aEnv of
      Nothing -> return q
      Just m' -> return $ qualifyWith m' (unqualify q)

ok :: Monad m => m ()
ok = return ()

-- |Run a 'WCM' action and return the list of messages
runOn :: WcState -> WCM a -> [Message]
runOn s f = sort $ warnings $ execState f s

-- ---------------------------------------------------------------------------
-- checkExports
-- ---------------------------------------------------------------------------

-- TODO: Add more checks (see GHC)
checkExports :: Maybe ExportSpec -> WCM ()
checkExports Nothing                      = ok
checkExports (Just (Exporting _ exports)) = do
  mapM_ visitExport exports
  reportUnusedGlobalVars
    where
      visitExport (Export _ qid) = visitQId qid
      visitExport _              = ok

-- ---------------------------------------------------------------------------
-- checkImports
-- ---------------------------------------------------------------------------

-- Check import declarations for multiply imported modules and multiply
-- imported/hidden values.
-- The function uses a map of the already imported or hidden entities to
-- collect the entities throughout multiple import statements.
checkImports :: [ImportDecl] -> WCM ()
checkImports = warnFor WarnMultipleImports . foldM_ checkImport Map.empty
  where
  checkImport env (ImportDecl pos mid _ _ spec) = case Map.lookup mid env of
    Nothing   -> setImportSpec env mid $ fromImpSpec spec
    Just ishs -> checkImportSpec env pos mid ishs spec

  checkImportSpec env _ mid (_, _)    Nothing = do
    report $ warnMultiplyImportedModule mid
    return env

  checkImportSpec env _ mid (is, hs) (Just (Importing _ is'))
    | null is && any (`notElem` hs) is' = do
        report $ warnMultiplyImportedModule mid
        setImportSpec env mid (is', hs)
    | null iis  = setImportSpec env mid (is' ++ is, hs)
    | otherwise = do
        mapM_ (report . warnMultiplyImportedSymbol mid . impName) iis
        setImportSpec env mid (unionBy cmpImport is' is, hs)
    where iis = intersectBy cmpImport is' is

  checkImportSpec env _ mid (is, hs) (Just (Hiding _ hs'))
    | null ihs  = setImportSpec env mid (is, hs' ++ hs)
    | otherwise = do
        mapM_ (report . warnMultiplyHiddenSymbol mid . impName) ihs
        setImportSpec env mid (is, unionBy cmpImport hs' hs)
    where ihs = intersectBy cmpImport hs' hs

  fromImpSpec Nothing                 = ([], [])
  fromImpSpec (Just (Importing _ is)) = (is, [])
  fromImpSpec (Just (Hiding    _ hs)) = ([], hs)

  setImportSpec env mid ishs = return $ Map.insert mid ishs env

  cmpImport (ImportTypeWith _ id1 cs1) (ImportTypeWith _ id2 cs2)
    = id1 == id2 && null (cs1 `intersect` cs2)
  cmpImport i1 i2 = impName i1 == impName i2

  impName (Import           _ v) = v
  impName (ImportTypeAll    _ t) = t
  impName (ImportTypeWith _ t _) = t

warnMultiplyImportedModule :: ModuleIdent -> Message
warnMultiplyImportedModule mid = spanInfoMessage mid $ hsep $ map text
  ["Module", moduleName mid, "is imported more than once"]

warnMultiplyImportedSymbol :: ModuleIdent -> Ident -> Message
warnMultiplyImportedSymbol mid ident = spanInfoMessage ident $ hsep $ map text
  [ "Symbol", escName ident, "from module", moduleName mid
  , "is imported more than once" ]

warnMultiplyHiddenSymbol :: ModuleIdent -> Ident -> Message
warnMultiplyHiddenSymbol mid ident = spanInfoMessage ident $ hsep $ map text
  [ "Symbol", escName ident, "from module", moduleName mid
  , "is hidden more than once" ]

-- ---------------------------------------------------------------------------
-- checkDeclGroup
-- ---------------------------------------------------------------------------

checkDeclGroup :: Bool -> [Decl ()] -> WCM ()
checkDeclGroup hasSig ds = do
  mapM_ insertDecl ds
  mapM_ (checkDecl hasSig) ds
  checkRuleAdjacency ds

checkLocalDeclGroup :: Bool -> [Decl ()] -> WCM ()
checkLocalDeclGroup hasSig ds = do
  mapM_ checkLocalDecl ds
  checkDeclGroup hasSig ds

-- ---------------------------------------------------------------------------
-- Find function rules which are disjoined
-- ---------------------------------------------------------------------------

checkRuleAdjacency :: [Decl a] -> WCM ()
checkRuleAdjacency decls = warnFor WarnDisjoinedRules
                         $ foldM_ check (mkIdent "", Map.empty) decls
  where
  check (prevId, env) (FunctionDecl p _ f _) = do
    cons <- isConsId f
    if cons || prevId == f
      then return (f, env)
      else case Map.lookup f env of
        Nothing -> return (f, Map.insert f p env)
        Just p' -> do
          report $ warnDisjoinedFunctionRules f (spanInfo2Pos p')
          return (f, env)
  check (_    , env) _                     = return (mkIdent "", env)

warnDisjoinedFunctionRules :: Ident -> Position -> Message
warnDisjoinedFunctionRules ident pos = spanInfoMessage ident $ hsep (map text
  [ "Rules for function", escName ident, "are disjoined" ])
  <+> parens (text "first occurrence at" <+> text (showLine pos))

checkDecl :: Bool -> Decl () -> WCM ()
checkDecl _      (DataDecl          _ _ vs cs _) = inNestedScope $ do
  mapM_ insertTypeVar   vs
  mapM_ checkConstrDecl cs
  reportUnusedTypeVars  vs
checkDecl _      (NewtypeDecl       _ _ vs nc _) = inNestedScope $ do
  mapM_ insertTypeVar   vs
  checkNewConstrDecl nc
  reportUnusedTypeVars vs
checkDecl _      (TypeDecl            _ _ vs ty) = inNestedScope $ do
  mapM_ insertTypeVar  vs
  checkTypeExpr ty
  reportUnusedTypeVars vs
checkDecl hasSig (FunctionDecl        p _ f eqs) = do
  sigs <- getDetSignatures
  case Map.lookup f sigs of
    Nothing -> checkFunctionDecl p f hasSig eqs
    Just _  -> do
      checkFunctionDecl p f True eqs
checkDecl hasSig (PatternDecl           _ p rhs) = checkPattern p >> checkRhs hasSig rhs
checkDecl _      (DefaultDecl             _ tys) = mapM_ checkTypeExpr tys
checkDecl _      (ClassDecl        _ _ _ _ _ ds) = do
  let clsSigs = concat [ map (,s) is | DetSig _ is s <- ds]
  modify (\s -> s { signatures = Map.fromList clsSigs `Map.union` signatures s})
  mapM_ (checkDecl False) ds
checkDecl _      (InstanceDecl p _ cx cls ty ds) = do
  checkOrphanInstance p cx cls ty
  checkMissingMethodImplementations p cls ds
  mid <- getModuleIdent
  tcEnv <- gets tyConsEnv
  let meths = case qualLookupTypeInfoUnique mid cls tcEnv of
        [TypeClass _ _ meths'] -> meths'
        _ -> internalError $ "Checks.WarnCheck.checkDecl: " ++ show cls
      go d@(FunctionDecl _ _ f _) = do
        let hasSig = isJust $ find ((==f) . methodName) meths >>= methodDetSchemeAnn
        checkDecl hasSig d
      go d = checkDecl False d
  mapM_ go ds
checkDecl _      _                             = ok

--TODO: Add shadowing warnings
checkConstrDecl :: ConstrDecl -> WCM ()
checkConstrDecl (ConstrDecl     _ c tys) = inNestedScope $ do
  visitId c
  mapM_ checkTypeExpr tys
checkConstrDecl (ConOpDecl _ ty1 op ty2) = inNestedScope $ do
  visitId op
  mapM_ checkTypeExpr [ty1, ty2]
checkConstrDecl (RecordDecl      _ c fs) = inNestedScope $ do
  visitId c
  mapM_ checkTypeExpr tys
  where
    tys = [ty | FieldDecl _ _ ty <- fs]

checkNewConstrDecl :: NewConstrDecl -> WCM ()
checkNewConstrDecl (NewConstrDecl _ c      ty) = do
  visitId c
  checkTypeExpr ty
checkNewConstrDecl (NewRecordDecl _ c (_, ty)) = do
  visitId c
  checkTypeExpr ty

checkTypeExpr :: TypeExpr -> WCM ()
checkTypeExpr (ConstructorType     _ qid) = visitQTypeId qid
checkTypeExpr (ApplyType       _ ty1 ty2) = mapM_ checkTypeExpr [ty1, ty2]
checkTypeExpr (VariableType          _ v) = visitTypeId v
checkTypeExpr (TupleType           _ tys) = mapM_ checkTypeExpr tys
checkTypeExpr (ListType             _ ty) = checkTypeExpr ty
checkTypeExpr (ArrowType       _ ty1 ty2) = mapM_ checkTypeExpr [ty1, ty2]
checkTypeExpr (ParenType            _ ty) = checkTypeExpr ty
checkTypeExpr (ForallType        _ vs ty) = do
  mapM_ insertTypeVar vs
  checkTypeExpr ty

-- Checks locally declared identifiers (i.e. functions and logic variables)
-- for shadowing
checkLocalDecl :: Decl a -> WCM ()
checkLocalDecl (FunctionDecl _ _ f _) = checkShadowing f
checkLocalDecl (FreeDecl        _ vs) = mapM_ (checkShadowing . varIdent) vs
checkLocalDecl (PatternDecl    _ p _) = checkPattern p
checkLocalDecl _                      = ok

checkFunctionDecl :: SpanInfo -> Ident -> Bool -> [Equation ()] -> WCM ()
checkFunctionDecl _ _ _ []  = ok
checkFunctionDecl p f hasSig eqs = inNestedScope $ do
  mapM_ (checkEquation hasSig) eqs
  checkFunctionPatternMatch p f hasSig eqs

checkFunctionPatternMatch :: SpanInfo -> Ident -> Bool -> [Equation ()] -> WCM ()
checkFunctionPatternMatch spi f hasSig eqs = do
  let pats = map (\(Equation _ lhs _) -> snd (flatLhs lhs)) eqs
  let guards = map eq2Guards eqs
  (nonExhaustive, overlapped, nondet) <- checkPatternMatching pats guards
  unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
    warnMissingPattern spi ("an equation for " ++ escName f) nonExhaustive
  when (not hasSig && (nondet || not (null overlapped))) $
    warnFor WarnOverlapping $ report $
    warnNondetOverlapping spi ("Function " ++ escName f)
  where eq2Guards :: Equation () -> [CondExpr ()]
        eq2Guards (Equation _ _ (GuardedRhs _ _ conds _)) = conds
        eq2Guards _ = []

-- Check an equation for warnings.
-- This is done in a seperate scope as the left-hand-side may introduce
-- new variables.
checkEquation :: Bool -> Equation () -> WCM ()
checkEquation hasSig (Equation _ lhs rhs) = inNestedScope $ do
  checkLhs lhs
  checkRhs hasSig rhs
  reportUnusedVars

checkLhs :: Lhs a -> WCM ()
checkLhs (FunLhs    _ _ ts) = do
  mapM_ checkPattern ts
  mapM_ (insertPattern False) ts
checkLhs (OpLhs spi t1 op t2) = checkLhs (FunLhs spi op [t1, t2])
checkLhs (ApLhs   _ lhs ts) = do
  checkLhs lhs
  mapM_ checkPattern ts
  mapM_ (insertPattern False) ts

checkPattern :: Pattern a -> WCM ()
checkPattern (VariablePattern          _ _ v) = checkShadowing v
checkPattern (ConstructorPattern    _ _ _ ps) = mapM_ checkPattern ps
checkPattern (InfixPattern     spi a p1 f p2) =
  checkPattern (ConstructorPattern spi a f [p1, p2])
checkPattern (ParenPattern               _ p) = checkPattern p
checkPattern (RecordPattern         _ _ _ fs) = mapM_ (checkField checkPattern) fs
checkPattern (TuplePattern              _ ps) = mapM_ checkPattern ps
checkPattern (ListPattern             _ _ ps) = mapM_ checkPattern ps
checkPattern (AsPattern                _ v p) = checkShadowing v >> checkPattern p
checkPattern (LazyPattern                _ p) = checkPattern p
checkPattern (FunctionPattern       _ _ _ ps) = mapM_ checkPattern ps
checkPattern (InfixFuncPattern spi a p1 f p2) =
  checkPattern (FunctionPattern spi a f [p1, p2])
checkPattern _                            = ok

-- Check the right-hand-side of an equation.
-- Because local declarations may introduce new variables, we need
-- another scope nesting.
checkRhs :: Bool -> Rhs () -> WCM ()
checkRhs hasSig (SimpleRhs _ _ e ds) = inNestedScope $ do
  checkLocalDeclGroup hasSig ds
  checkExpr hasSig e
  reportUnusedVars
checkRhs hasSig (GuardedRhs _ _ ce ds) = inNestedScope $ do
  checkLocalDeclGroup hasSig ds
  mapM_ (checkCondExpr hasSig) ce
  reportUnusedVars

checkCondExpr :: Bool -> CondExpr () -> WCM ()
checkCondExpr hasSig (CondExpr _ c e) = checkExpr hasSig c >> checkExpr hasSig e

checkExpr :: Bool -> Expression () -> WCM ()
checkExpr _      (Variable            _ _ v) = visitQId v
checkExpr hasSig (Paren                 _ e) = checkExpr hasSig e
checkExpr hasSig (Typed               _ e _) = checkExpr hasSig e
checkExpr hasSig (Record           _ _ _ fs) = mapM_ (checkField (checkExpr hasSig)) fs
checkExpr hasSig (RecordUpdate       _ e fs) = do
  checkExpr hasSig e
  mapM_ (checkField (checkExpr hasSig)) fs
checkExpr hasSig (Tuple                _ es) = mapM_ (checkExpr hasSig) es
checkExpr hasSig (List               _ _ es) = mapM_ (checkExpr hasSig) es
checkExpr hasSig (ListCompr         _ e sts) = checkStatements  hasSig sts e
checkExpr hasSig (EnumFrom              _ e) = checkExpr hasSig e
checkExpr hasSig (EnumFromThen      _ e1 e2) = mapM_ (checkExpr hasSig) [e1, e2]
checkExpr hasSig (EnumFromTo        _ e1 e2) = mapM_ (checkExpr hasSig) [e1, e2]
checkExpr hasSig (EnumFromThenTo _ e1 e2 e3) = mapM_ (checkExpr hasSig) [e1, e2, e3]
checkExpr hasSig (UnaryMinus            _ e) = checkExpr hasSig e
checkExpr hasSig (Apply             _ e1 e2) = mapM_ (checkExpr hasSig) [e1, e2]
checkExpr hasSig (InfixApply     _ e1 op e2) = do
  visitQId (opName op)
  mapM_ (checkExpr hasSig) [e1, e2]
checkExpr hasSig (LeftSection         _ e _) = checkExpr hasSig e
checkExpr hasSig (RightSection        _ _ e) = checkExpr hasSig e
checkExpr hasSig (Lambda             _ ps e) = inNestedScope $ do
  mapM_ checkPattern ps
  mapM_ (insertPattern False) ps
  checkExpr hasSig e
  reportUnusedVars
checkExpr hasSig (Let              _ _ ds e) = inNestedScope $ do
  checkLocalDeclGroup hasSig ds
  checkExpr hasSig e
  reportUnusedVars
checkExpr hasSig (Do              _ _ sts e) = checkStatements hasSig sts e
checkExpr hasSig (IfThenElse     _ e1 e2 e3) = mapM_ (checkExpr hasSig) [e1, e2, e3]
checkExpr hasSig (Case      spi _ ct e alts) = do
  checkExpr hasSig e
  mapM_ (checkAlt hasSig) alts
  checkCaseAlts spi ct hasSig alts
checkExpr _      _                       = ok

checkStatements :: Bool -> [Statement ()] -> Expression () -> WCM ()
checkStatements hasSig []     e = checkExpr hasSig e
checkStatements hasSig (s:ss) e = inNestedScope $ do
  checkStatement hasSig s >> checkStatements hasSig ss e
  reportUnusedVars

checkStatement :: Bool -> Statement () -> WCM ()
checkStatement hasSig (StmtExpr    _ e) =
  checkExpr hasSig e
checkStatement hasSig (StmtDecl _ _ ds) =
  checkLocalDeclGroup hasSig ds
checkStatement hasSig (StmtBind _  p e) = do
  checkPattern p >> insertPattern False p
  checkExpr hasSig e

checkAlt :: Bool -> Alt () -> WCM ()
checkAlt hasSig (Alt _ p rhs) = inNestedScope $ do
  checkPattern p >> insertPattern False p
  checkRhs hasSig rhs
  reportUnusedVars

checkField :: (a -> WCM ()) -> Field a -> WCM ()
checkField check (Field _ _ x) = check x

-- -----------------------------------------------------------------------------
-- Check for orphan instances
-- -----------------------------------------------------------------------------

checkOrphanInstance :: SpanInfo -> Context -> QualIdent -> TypeExpr -> WCM ()
checkOrphanInstance p cx cls ty = warnFor WarnOrphanInstances $ do
  m <- getModuleIdent
  tcEnv <- gets tyConsEnv
  let ocls = getOrigName m cls tcEnv
      otc  = getOrigName m tc  tcEnv
  unless (isLocalIdent m ocls || isLocalIdent m otc) $ report $
    warnOrphanInstance p $ pPrint $
    InstanceDecl p WhitespaceLayout cx cls ty []
  where tc = typeConstr ty

warnOrphanInstance :: SpanInfo -> Doc -> Message
warnOrphanInstance spi doc = spanInfoMessage spi $ text "Orphan instance:" <+> doc

-- -----------------------------------------------------------------------------
-- Check for missing method implementations
-- -----------------------------------------------------------------------------

checkMissingMethodImplementations :: SpanInfo -> QualIdent -> [Decl a] -> WCM ()
checkMissingMethodImplementations p cls ds = warnFor WarnMissingMethods $ do
  m <- getModuleIdent
  tcEnv <- gets tyConsEnv
  clsEnv <- gets classEnv
  let ocls = getOrigName m cls tcEnv
      ms   = visibleClassMethods ocls clsEnv
  mapM_ (report . warnMissingMethodImplementation p) $
    filter ((null fs ||) . not . flip (hasDefaultImpl ocls) clsEnv) $ ms \\ fs
  where fs = map unRenameIdent $ concatMap impls ds

warnMissingMethodImplementation :: SpanInfo -> Ident -> Message
warnMissingMethodImplementation spi f = spanInfoMessage spi $ hsep $ map text
  ["No explicit implementation for method", escName f]

-- -----------------------------------------------------------------------------
-- Check for missing type signatures
-- -----------------------------------------------------------------------------

-- |Check if every top-level function has an accompanying type signature.
-- For external function declarations, this check is already performed
-- during syntax checking.
checkMissingTypeSignatures :: [Decl a] -> WCM ()
checkMissingTypeSignatures ds = warnFor WarnMissingSignatures $ do
  let typedFs   = [f | TypeSig       _ fs _ <- ds, f <- fs]
      untypedFs = [f | FunctionDecl _ _ f _ <- ds, f `notElem` typedFs]
  unless (null untypedFs) $ do
    mid   <- getModuleIdent
    tyScs <- mapM getTyScheme untypedFs
    mapM_ report $ zipWith (warnMissingTypeSignature mid) untypedFs tyScs

getTyScheme :: Ident -> WCM TypeScheme
getTyScheme q = do
  m     <- getModuleIdent
  tyEnv <- gets valueEnv
  return $ case qualLookupValue (qualifyWith m q) tyEnv of
    [Value  _ _ _ tys] -> tys
    _ -> internalError $ "Checks.WarnCheck.getTyScheme: " ++ show q

warnMissingTypeSignature :: ModuleIdent -> Ident -> TypeScheme -> Message
warnMissingTypeSignature mid i tys = spanInfoMessage i $ fsep
  [ text "Top-level binding with no type signature:"
  , nest 2 $ text (showIdent i) <+> text "::" <+> ppTypeScheme mid tys
  ]

-- -----------------------------------------------------------------------------
-- Check for overlapping module alias names
-- -----------------------------------------------------------------------------

-- check if module aliases in import declarations overlap with the module name
-- or another module alias

checkModuleAlias :: [ImportDecl] -> WCM ()
checkModuleAlias is = do
  mid <- getModuleIdent
  let alias      = catMaybes [a | ImportDecl _ _ _ a _ <- is]
      modClash   = [a | a <- alias, a == mid]
      aliasClash = findMultiples alias
  unless (null   modClash) $ mapM_ (report . warnModuleNameClash) modClash
  unless (null aliasClash) $ mapM_ (report . warnAliasNameClash ) aliasClash

warnModuleNameClash :: ModuleIdent -> Message
warnModuleNameClash mid = spanInfoMessage mid $ hsep $ map text
  ["The module alias", escModuleName mid
  , "overlaps with the current module name"]

warnAliasNameClash :: [ModuleIdent] -> Message
warnAliasNameClash []         = internalError
  "WarnCheck.warnAliasNameClash: empty list"
warnAliasNameClash mids = spanInfoMessage (head mids) $ text
  "Overlapping module aliases" $+$ nest 2 (vcat (map myppAlias mids))
  where myppAlias mid =
          ppLine (getPosition mid) <> text ":" <+> text (escModuleName mid)

-- -----------------------------------------------------------------------------
-- Check for overlapping/unreachable and non-exhaustive case alternatives
-- -----------------------------------------------------------------------------

checkCaseAlts :: SpanInfo -> CaseType -> Bool -> [Alt ()] -> WCM ()
checkCaseAlts _   _  _      []   = ok
checkCaseAlts spi ct hasSig alts = do
  let spis = map (\(Alt s _ _) -> s) alts
  let pats = map (\(Alt _ pat _) -> [pat]) alts
  let guards = map alt2Guards alts
  (nonExhaustive, overlapped, nondet) <- checkPatternMatching pats guards
  case ct of
    Flex -> do
      unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
        warnMissingPattern spi "an fcase alternative" nonExhaustive
      when (not hasSig && (nondet || not (null overlapped)))
        $ warnFor WarnOverlapping $ report
        $ warnNondetOverlapping spi "An fcase expression"
    Rigid -> do
      unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
        warnMissingPattern spi "a case alternative" nonExhaustive
      unless (null overlapped) $ mapM_ ((warnFor WarnOverlapping . report) .
                                        (\(i, pat) -> warnUnreachablePattern (spis !! i) pat))
                                  overlapped
  where alt2Guards :: Alt () -> [CondExpr ()]
        alt2Guards (Alt _ _ (GuardedRhs _ _ conds _)) = conds
        alt2Guards _ = []

-- -----------------------------------------------------------------------------
-- Check for non-exhaustive and overlapping patterns.
-- For an example, consider the following function definition:
-- @
-- f [True]    = 0
-- f (False:_) = 1
-- @
-- In this declaration, the following patterns are not matched:
-- @
-- [] _
-- (True:_:_)
-- @
-- This is identified and reported by the following code,, both for pattern
-- matching in function declarations and (f)case expressions.
-- -----------------------------------------------------------------------------

checkPatternMatching :: [[Pattern ()]] -> [[CondExpr ()]]
                     -> WCM ([ExhaustivePats], [OverlappingPats], Bool)
checkPatternMatching pats guards = do
  -- 1. We simplify the patterns by removing syntactic sugar temporarily
  --    for a simpler implementation.
  simplePats <- mapM (mapM simplifyPat) pats
  -- 2. We compute missing and used pattern matching alternatives
  (missing, used, nondet) <- processEqs (zip3 [0..] simplePats guards)
  -- 3. If any, we report the missing patterns, whereby we re-add the syntactic
  --    sugar removed in step (1) for a more precise output.
  nonExhaustive <- mapM tidyExhaustivePats missing
  let overlap = [(i, eqn) | (i, eqn) <- zip [0..] pats, i `IntSet.notMember` used]
  return (nonExhaustive, overlap, nondet)

-- |Simplify a 'Pattern' until it only consists of
--   * Variables
--   * Integer, Float or Char literals
--   * Constructors
-- All other patterns like as-patterns, list patterns and alike are desugared.
simplifyPat :: Pattern () -> WCM (Pattern ())
simplifyPat p@(LiteralPattern        _ _ l) = return $ case l of
  String s -> simplifyListPattern $ map (LiteralPattern NoSpanInfo () . Char) s
  _        -> p
simplifyPat (NegativePattern       spi a l) =
  return $ LiteralPattern spi a (negateLit l)
  where
  negateLit (Int   n) = Int   (-n)
  negateLit (Float d) = Float (-d)
  negateLit x         = x
simplifyPat v@(VariablePattern       _ _ _) = return v
simplifyPat (ConstructorPattern spi a c ps) =
  ConstructorPattern spi a c <$> mapM simplifyPat ps
simplifyPat (InfixPattern    spi a p1 c p2) =
  ConstructorPattern spi a c <$> mapM simplifyPat [p1, p2]
simplifyPat (ParenPattern              _ p) = simplifyPat p
simplifyPat (RecordPattern        _ _ c fs) = do
  (_, ls) <- getAllLabels c
  let ps = map (getPattern (map field2Tuple fs)) ls
  simplifyPat (ConstructorPattern NoSpanInfo () c ps)
  where
    getPattern fs' l' =
      fromMaybe wildPat (lookup l' [(unqualify l, p) | (l, p) <- fs'])
simplifyPat (TuplePattern            _ ps) =
  ConstructorPattern NoSpanInfo () (qTupleId (length ps))
    <$> mapM simplifyPat ps
simplifyPat (ListPattern           _ _ ps) =
  simplifyListPattern `liftM` mapM simplifyPat ps
simplifyPat (AsPattern             _ _ p) = simplifyPat p
simplifyPat (LazyPattern             _ _) = return wildPat
simplifyPat (FunctionPattern     _ _ _ _) = return wildPat
simplifyPat (InfixFuncPattern  _ _ _ _ _) = return wildPat

getAllLabels :: QualIdent -> WCM (QualIdent, [Ident])
getAllLabels c = do
  tyEnv <- gets valueEnv
  case qualLookupValue c tyEnv of
    [DataConstructor qc _ ls _] -> return (qc, ls)
    _                           -> internalError $
          "Checks.WarnCheck.getAllLabels: " ++ show c

-- |Create a simplified list pattern by applying @:@ and @[]@.
simplifyListPattern :: [Pattern ()] -> Pattern ()
simplifyListPattern =
  foldr (\p1 p2 -> ConstructorPattern NoSpanInfo () qConsId [p1, p2])
        (ConstructorPattern NoSpanInfo () qNilId [])

-- |'ExhaustivePats' describes those pattern missing for an exhaustive
-- pattern matching, where a value can be thought of as a missing equation.
-- The first component contains the unmatched patterns, while the second
-- pattern contains an identifier and the literals matched for this identifier.
--
-- This is necessary when checking literal patterns because of the sheer
-- number of possible patterns. Missing literals are therefore converted
-- into the form @ ... x ... with x `notElem` [l1, ..., ln]@.
type EqnPats = [Pattern ()]
type EqnGuards = [CondExpr ()]
type EqnNo   = Int
type EqnInfo = (EqnNo, EqnPats, EqnGuards)

type ExhaustivePats = (EqnPats, [(Ident, [Literal])])
type OverlappingPats = (EqnNo, EqnPats)
type EqnSet  = IntSet.IntSet

-- |Compute the missing pattern by inspecting the first patterns and
-- categorize them as literal, constructor or variable patterns.
processEqs :: [EqnInfo] -> WCM ([ExhaustivePats], EqnSet, Bool)
processEqs []              = return ([], IntSet.empty, False)
processEqs eqs@((n, ps, gs):eqs')
  | null ps                = if guardsExhaustive then return ([], IntSet.singleton n, length eqs > 1)
                                                 else do -- Current expression is guarded, thus potentially
                                                         -- non-exhaustive. Therefore process remaining expressions.
                                                         (missing', used', _) <- processEqs eqs'
                                                         return (missing', IntSet.insert n used', length eqs > 1)
  | any isLitPat firstPats = processLits eqs
  | any isConPat firstPats = processCons eqs
  | all isVarPat firstPats = processVars eqs
  | otherwise              = internalError "Checks.WarnCheck.processEqs"
  where firstPats = map firstPat eqs
        guardsExhaustive = null gs || any guardAlwaysTrue gs
        guardAlwaysTrue :: CondExpr () -> Bool
        guardAlwaysTrue (CondExpr _ e _) = case e of
          Constructor _ _ q -> qidAlwaysTrue q
          Variable    _ _ q -> qidAlwaysTrue q
          _ -> False
        qidAlwaysTrue :: QualIdent -> Bool
        qidAlwaysTrue q = elem (idName $ qidIdent q) ["True", "success", "otherwise"]


-- |Literal patterns are checked by extracting the matched literals
--  and constructing a pattern for any missing case.
processLits :: [EqnInfo] -> WCM ([ExhaustivePats], EqnSet, Bool)
processLits []       = error "WarnCheck.processLits"
processLits qs@(q:_) = do
  -- Check any patterns starting with the literals used
  (missing1, used1, nd1) <- processUsedLits usedLits qs
  if null defaults
    then return $ (defaultPat : missing1, used1, nd1)
    else do
      -- Missing patterns for the default alternatives
      (missing2, used2, nd2) <- processEqs defaults
      return ( [ (wildPat : ps, cs) | (ps, cs) <- missing2 ] ++ missing1
             , IntSet.union used1 used2, nd1 || nd2 )
  where
  -- The literals occurring in the patterns
  usedLits   = nub $ concatMap (getLit . firstPat) qs
  -- default alternatives (variable pattern)
  defaults   = [ shiftPat q' | q' <- qs, isVarPat (firstPat q') ]
  -- Pattern for all non-matched literals
  defaultPat = ( VariablePattern NoSpanInfo () newVar :
                   replicate (length (snd3 q) - 1) wildPat
               , [(newVar, usedLits)]
               )
  newVar     = mkIdent "x"

-- |Construct exhaustive patterns starting with the used literals
processUsedLits :: [Literal] -> [EqnInfo]
                -> WCM ([ExhaustivePats], EqnSet, Bool)
processUsedLits lits qs = do
  (eps, idxs, nds) <- unzip3 `liftM` mapM process lits
  return (concat eps, IntSet.unions idxs, or nds)
  where
  process lit = do
    let qs' = [shiftPat q | q <- qs, isVarLit lit (firstPat q)]
        ovlp = length qs' > 1
    (missing, used, nd) <- processEqs qs'
    return ( map (\(xs, ys) -> (LiteralPattern NoSpanInfo () lit : xs, ys))
                 missing
           , used
           , nd && ovlp
           )

-- |Constructor patterns are checked by extracting the matched constructors
--  and constructing a pattern for any missing case.
processCons :: [EqnInfo] -> WCM ([ExhaustivePats], EqnSet, Bool)
processCons []       = error "WarnCheck.processCons"
processCons qs@(q:_) = do
  -- Compute any missing patterns starting with the used constructors
  (missing1, used1, nd) <- processUsedCons used_cons qs
  -- Determine unused constructors
  unused   <- getUnusedCons (map fst used_cons)
  if null unused
    then return (missing1, used1, nd)
    else if null defaults
      then return $ (map defaultPat unused ++ missing1, used1, nd)
      else do
        -- Missing patterns for the default alternatives
        (missing2, used2, nd2) <- processEqs defaults
        return ( [ (mkPattern c : ps, cs) | c <- unused, (ps, cs) <- missing2 ]
                  ++ missing1
               , IntSet.union used1 used2, nd || nd2)
  where
  -- used constructors (occurring in a pattern)
  used_cons    = nub $ concatMap (getCon . firstPat) qs
  -- default alternatives (variable pattern)
  defaults     = [ shiftPat q' | q' <- qs, isVarPat (firstPat q') ]
  -- Pattern for a non-matched constructors
  defaultPat c = (mkPattern c : replicate (length (snd3 q) - 1) wildPat, [])
  mkPattern  c = ConstructorPattern NoSpanInfo ()
                  (qualifyLike (fst $ head used_cons) (constrIdent c))
                  (replicate (length $ constrTypes c) wildPat)

-- |Construct exhaustive patterns starting with the used constructors
processUsedCons :: [(QualIdent, Int)] -> [EqnInfo]
                -> WCM ([ExhaustivePats], EqnSet, Bool)
processUsedCons cons qs = do
  (eps, idxs, nds) <- unzip3 `liftM` mapM process cons
  return (concat eps, IntSet.unions idxs, or nds)
  where
  process (c, a) = do
    let qs' = [ removeFirstCon c a q | q <- qs , isVarCon c (firstPat q)]
        ovlp = length qs' > 1
    (missing, used, nd) <- processEqs qs'
    return (map (\(xs, ys) -> (makeCon c a xs, ys)) missing, used, nd && ovlp)

  makeCon c a ps = let (args, rest) = splitAt a ps
                   in ConstructorPattern NoSpanInfo () c args : rest

  removeFirstCon c a (n, p:ps, gs)
    | isVarPat p = (n, replicate a wildPat ++ ps, gs)
    | isCon c  p = (n, patArgs p           ++ ps, gs)
  removeFirstCon _ _ _ = internalError "Checks.WarnCheck.removeFirstCon"

-- |Variable patterns are exhaustive, so they are checked by simply
-- checking the following patterns.
processVars :: [EqnInfo] -> WCM ([ExhaustivePats], EqnSet, Bool)
processVars []               = error "WarnCheck.processVars"
processVars eqs@((n, _, _) : _) = do
  let ovlp = length eqs > 1
  (missing, used, nd) <- processEqs (map shiftPat eqs)
  return ( map (\(xs, ys) -> (wildPat : xs, ys)) missing
         , IntSet.insert n used, nd && ovlp)

-- |Return the constructors of a type not contained in the list of constructors.
getUnusedCons :: [QualIdent] -> WCM [DataConstr]
getUnusedCons []       = internalError "Checks.WarnCheck.getUnusedCons"
getUnusedCons qs@(q:_) = do
  allCons <- getConTy q >>= getTyCons . rootOfType . arrowBase
  return [c | c <- allCons, (constrIdent c) `notElem` map unqualify qs]

-- |Retrieve the type of a given constructor.
getConTy :: QualIdent -> WCM Type
getConTy q = do
  tyEnv <- gets valueEnv
  tcEnv <- gets tyConsEnv
  case qualLookupValue q tyEnv of
    [DataConstructor  _ _ _ (ForAll _ (PredType _ ty))] -> return ty
    [NewtypeConstructor _ _ (ForAll _ (PredType _ ty))] -> return ty
    _ -> case qualLookupTypeInfo q tcEnv of
      [AliasType _ _ _ ty] -> return ty
      _ -> internalError $ "Checks.WarnCheck.getConTy: " ++ show q

-- |Retrieve all constructors of a given type.
getTyCons :: QualIdent -> WCM [DataConstr]
getTyCons tc = do
  tc'   <- unAlias tc
  tcEnv <- gets tyConsEnv
  let getTyCons' :: [TypeInfo] -> Either String [DataConstr]
      getTyCons' ti = case ti of
        [DataType     _ _ cs] -> Right cs
        [RenamingType _ _ nc] -> Right $ [nc]
        _                     -> Left $ "Checks.WarnCheck.getTyCons: " ++ show tc ++ ' ' : show ti ++ '\n' : show tcEnv
      csResult =  getTyCons' (qualLookupTypeInfo tc tcEnv)
             <||> getTyCons' (qualLookupTypeInfo tc' tcEnv)
             <||> getTyCons' (lookupTypeInfo (unqualify tc) tcEnv) -- Fall back on unqualified lookup if qualified doesn't work
  case csResult of
    Right cs -> return cs
    Left err -> internalError err
  where
    Left _  <||> r = r
    Right x <||> _ = Right x

-- |Resugar the exhaustive patterns previously desugared at 'simplifyPat'.
tidyExhaustivePats :: ExhaustivePats -> WCM ExhaustivePats
tidyExhaustivePats (xs, ys) = mapM tidyPat xs >>= \xs' -> return (xs', ys)

-- |Resugar a pattern previously desugared at 'simplifyPat', i.e.
--   * Convert a tuple constructor pattern into a tuple pattern
--   * Convert a list constructor pattern representing a finite list
--     into a list pattern
tidyPat :: Pattern () -> WCM (Pattern ())
tidyPat p@(LiteralPattern        _ _ _) = return p
tidyPat p@(VariablePattern       _ _ _) = return p
tidyPat p@(ConstructorPattern _ _ c ps)
  | isQTupleId c                      =
    TuplePattern NoSpanInfo `liftM` mapM tidyPat ps
  | c == qConsId && isFiniteList p    =
    ListPattern NoSpanInfo () `liftM` mapM tidyPat (unwrapFinite p)
  | c == qConsId                      = unwrapInfinite p
  | otherwise                         =
    ConstructorPattern NoSpanInfo () c `liftM` mapM tidyPat ps
  where
  isFiniteList (ConstructorPattern _ _ d []     ) = d == qNilId
  isFiniteList (ConstructorPattern _ _ d [_, e2])
                                   | d == qConsId = isFiniteList e2
  isFiniteList _                                  = False

  unwrapFinite (ConstructorPattern _ _ _ []     ) = []
  unwrapFinite (ConstructorPattern _ _ _ [p1,p2]) = p1 : unwrapFinite p2
  unwrapFinite pat
    = internalError $ "WarnCheck.tidyPat.unwrapFinite: " ++ show pat

  unwrapInfinite (ConstructorPattern _ a d [p1,p2]) =
    liftM2 (flip (InfixPattern NoSpanInfo a) d) (tidyPat p1) (unwrapInfinite p2)
  unwrapInfinite p0                                 = return p0

tidyPat p = internalError $ "Checks.WarnCheck.tidyPat: " ++ show p

-- |Get the first pattern of a list.
firstPat :: EqnInfo -> Pattern ()
firstPat (_, [],    _) = internalError "Checks.WarnCheck.firstPat: empty list"
firstPat (_, (p:_), _) = p

-- |Drop the first pattern of a list.
shiftPat :: EqnInfo -> EqnInfo
shiftPat (_, [],     _ ) = internalError "Checks.WarnCheck.shiftPat: empty list"
shiftPat (n, (_:ps), gs) = (n, ps, gs)

-- |Wildcard pattern.
wildPat :: Pattern ()
wildPat = VariablePattern NoSpanInfo () anonId

-- |Retrieve any literal out of a pattern.
getLit :: Pattern a -> [Literal]
getLit (LiteralPattern _ _ l) = [l]
getLit _                      = []

-- |Retrieve the constructor name and its arity for a pattern.
getCon :: Pattern a -> [(QualIdent, Int)]
getCon (ConstructorPattern _ _ c ps) = [(c, length ps)]
getCon _                             = []

-- |Is a pattern a variable or literal pattern?
isVarLit :: Literal -> Pattern a -> Bool
isVarLit l p = isVarPat p || isLit l p

-- |Is a pattern a variable or a constructor pattern with the given constructor?
isVarCon :: QualIdent -> Pattern a -> Bool
isVarCon c p = isVarPat p || isCon c p

-- |Is a pattern a pattern matching for the given constructor?
isCon :: QualIdent -> Pattern a -> Bool
isCon c (ConstructorPattern _ _ d _) = c == d
isCon _ _                            = False

-- |Is a pattern a pattern matching for the given literal?
isLit :: Literal -> Pattern a -> Bool
isLit l (LiteralPattern _ _ m) = l == m
isLit _ _                      = False

-- |Is a pattern a literal pattern?
isLitPat :: Pattern a -> Bool
isLitPat (LiteralPattern  _ _ _) = True
isLitPat _                       = False

-- |Is a pattern a variable pattern?
isVarPat :: Pattern a -> Bool
isVarPat (VariablePattern _ _ _) = True
isVarPat _                       = False

-- |Is a pattern a constructor pattern?
isConPat :: Pattern a -> Bool
isConPat (ConstructorPattern _ _ _ _) = True
isConPat _                            = False

-- |Retrieve the arguments of a pattern.
patArgs :: Pattern a -> [Pattern a]
patArgs (ConstructorPattern _ _ _ ps) = ps
patArgs _                             = []

-- |Warning message for non-exhaustive patterns.
-- To shorten the output only the first 'maxPattern' are printed,
-- additional pattern are abbreviated by dots.
warnMissingPattern :: SpanInfo -> String -> [ExhaustivePats] -> Message
warnMissingPattern spi loc pats = spanInfoMessage spi
  $   text "Pattern matches are non-exhaustive"
  $+$ text "In" <+> text loc <> char ':'
  $+$ nest 2 (text "Patterns not matched:" $+$ nest 2 (vcat (ppExPats pats)))
  where
  ppExPats ps
    | length ps > maxPattern = ppPats ++ [text "..."]
    | otherwise              = ppPats
    where ppPats = map ppExPat (take maxPattern ps)
  ppExPat (ps, cs)
    | null cs   = ppPats
    | otherwise = ppPats <+> text "with" <+> hsep (map ppCons cs)
    where ppPats = hsep (map (pPrintPrec 2) ps)
  ppCons (i, lits) = pPrint i <+> text "`notElem`"
            <+> pPrintPrec 0 (List NoSpanInfo () (map (Literal NoSpanInfo ()) lits))

-- |Warning message for unreachable patterns.
-- To shorten the output only the first 'maxPattern' are printed,
-- additional pattern are abbreviated by dots.
warnUnreachablePattern :: SpanInfo  -> [Pattern a] -> Message
warnUnreachablePattern spi pats = spanInfoMessage spi
  $   text "Pattern matches are potentially unreachable"
  $+$ text "In a case alternative:"
  $+$ nest 2 (ppPat pats <+> text "->" <+> text "...")
  where
  ppPat ps = hsep (map (pPrintPrec 2) ps)

-- |Maximum number of missing patterns to be shown.
maxPattern :: Int
maxPattern = 4

warnNondetOverlapping :: SpanInfo -> String -> Message
warnNondetOverlapping spi loc = spanInfoMessage spi $
  text loc <+> text "is potentially non-deterministic due to overlapping rules"
  $+$ text "To suppress this warning, add a determinism annotation"

-- -----------------------------------------------------------------------------

checkShadowing :: Ident -> WCM ()
checkShadowing x = do
  warnFor WarnNameShadowing $
    shadowsVar x >>= maybe ok (report . warnShadowing x)
  warnFor WarnImportNameShadowing $
    shadowsImport x >>= maybe ok (report . warnShadowing x)

reportUnusedVars :: WCM ()
reportUnusedVars = reportAllUnusedVars WarnUnusedBindings

reportUnusedGlobalVars :: WCM ()
reportUnusedGlobalVars = reportAllUnusedVars WarnUnusedGlobalBindings

reportAllUnusedVars :: WarnFlag -> WCM ()
reportAllUnusedVars wFlag = warnFor wFlag $ do
  unused <- returnUnrefVars
  unless (null unused) $ mapM_ report $ map warnUnrefVar unused

reportUnusedTypeVars :: [Ident] -> WCM ()
reportUnusedTypeVars vs = warnFor WarnUnusedBindings $ do
  unused <- filterM isUnrefTypeVar vs
  unless (null unused) $ mapM_ report $ map warnUnrefTypeVar unused

-- ---------------------------------------------------------------------------
-- For detecting unreferenced variables, the following functions update the
-- current check state by adding identifiers occuring in declaration left hand
-- sides.

insertDecl :: Decl a -> WCM ()
insertDecl (DataDecl      _ d _ cs _) = do
  insertTypeConsId d
  mapM_ insertConstrDecl cs
insertDecl (ExternalDataDecl   _ d _) = insertTypeConsId d
insertDecl (NewtypeDecl   _ d _ nc _) = do
  insertTypeConsId d
  insertNewConstrDecl nc
insertDecl (TypeDecl        _ t _ ty) = do
  insertTypeConsId t
  insertTypeExpr ty
insertDecl (FunctionDecl     _ _ f _) = do
  cons <- isConsId f
  unless cons $ insertVar f
insertDecl (ExternalDecl        _ vs) = mapM_ (insertVar . varIdent) vs
insertDecl (PatternDecl        _ p _) = insertPattern False p
insertDecl (FreeDecl            _ vs) = mapM_ (insertVar . varIdent) vs
insertDecl (ClassDecl _ _ _ cls _ ds) = do
  insertTypeConsId cls
  mapM_ insertVar $ concatMap methods ds
insertDecl _                          = ok

insertTypeExpr :: TypeExpr -> WCM ()
insertTypeExpr (VariableType       _ _) = ok
insertTypeExpr (ConstructorType    _ _) = ok
insertTypeExpr (ApplyType    _ ty1 ty2) = mapM_ insertTypeExpr [ty1,ty2]
insertTypeExpr (TupleType        _ tys) = mapM_ insertTypeExpr tys
insertTypeExpr (ListType          _ ty) = insertTypeExpr ty
insertTypeExpr (ArrowType    _ ty1 ty2) = mapM_ insertTypeExpr [ty1,ty2]
insertTypeExpr (ParenType         _ ty) = insertTypeExpr ty
insertTypeExpr (ForallType      _ _ ty) = insertTypeExpr ty

insertConstrDecl :: ConstrDecl -> WCM ()
insertConstrDecl (ConstrDecl _    c _) = insertConsId c
insertConstrDecl (ConOpDecl  _ _ op _) = insertConsId op
insertConstrDecl (RecordDecl _    c _) = insertConsId c

insertNewConstrDecl :: NewConstrDecl -> WCM ()
insertNewConstrDecl (NewConstrDecl _ c _) = insertConsId c
insertNewConstrDecl (NewRecordDecl _ c _) = insertConsId c

-- 'fp' indicates whether 'checkPattern' deals with the arguments
-- of a function pattern or not.
-- Since function patterns are not recognized before syntax check, it is
-- necessary to determine whether a constructor pattern represents a
-- constructor or a function.
insertPattern :: Bool -> Pattern a -> WCM ()
insertPattern fp (VariablePattern       _ _ v) = do
  cons <- isConsId v
  unless cons $ do
    var <- isVarId v
    if and [fp, var, not (isAnonId v)] then visitId v else insertVar v
insertPattern fp (ConstructorPattern _ _ c ps) = do
  cons <- isQualConsId c
  mapM_ (insertPattern (not cons || fp)) ps
insertPattern fp (InfixPattern    spi a p1 c p2)
  = insertPattern fp (ConstructorPattern spi a c [p1, p2])
insertPattern fp (ParenPattern          _ p) = insertPattern fp p
insertPattern fp (RecordPattern    _ _ _ fs) = mapM_ (insertFieldPattern fp) fs
insertPattern fp (TuplePattern         _ ps) = mapM_ (insertPattern fp) ps
insertPattern fp (ListPattern        _ _ ps) = mapM_ (insertPattern fp) ps
insertPattern fp (AsPattern           _ v p) = insertVar v >> insertPattern fp p
insertPattern fp (LazyPattern           _ p) = insertPattern fp p
insertPattern _  (FunctionPattern  _ _ f ps) = do
  visitQId f
  mapM_ (insertPattern True) ps
insertPattern _  (InfixFuncPattern spi a p1 f p2)
  = insertPattern True (FunctionPattern spi a f [p1, p2])
insertPattern _ _ = ok

insertFieldPattern :: Bool -> Field (Pattern a) -> WCM ()
insertFieldPattern fp (Field _ _ p) = insertPattern fp p

-- ---------------------------------------------------------------------------

-- Data type for distinguishing identifiers as either (type) constructors or
-- (type) variables (including functions).
data IdInfo
  = ConsInfo           -- ^ Constructor
  | VarInfo Ident Bool -- ^ Variable with original definition (for position)
                       --   and used flag
  deriving Show

isVariable :: IdInfo -> Bool
isVariable (VarInfo _ _) = True
isVariable _             = False

getVariable :: IdInfo -> Maybe Ident
getVariable (VarInfo v _) = Just v
getVariable _             = Nothing

isConstructor :: IdInfo -> Bool
isConstructor ConsInfo = True
isConstructor _        = False

variableVisited :: IdInfo -> Bool
variableVisited (VarInfo _ v) = v
variableVisited _             = True

visitVariable :: IdInfo -> IdInfo
visitVariable (VarInfo v _) = VarInfo v True
visitVariable  info         = info

insertScope :: QualIdent -> IdInfo -> WCM ()
insertScope qid info = modifyScope $ qualBindNestEnv qid info

insertVar :: Ident -> WCM ()
insertVar v = unless (isAnonId v) $ do
  known <- isKnownVar v
  if known then visitId v else insertScope (commonId v) (VarInfo v False)

insertTypeVar :: Ident -> WCM ()
insertTypeVar v = unless (isAnonId v)
                $ insertScope (typeId v) (VarInfo v False)

insertConsId :: Ident -> WCM ()
insertConsId c = insertScope (commonId c) ConsInfo

insertTypeConsId :: Ident -> WCM ()
insertTypeConsId c = insertScope (typeId c) ConsInfo

isVarId :: Ident -> WCM Bool
isVarId v = gets (isVar $ commonId v)

isConsId :: Ident -> WCM Bool
isConsId c = gets (isCons $ qualify c)

isQualConsId :: QualIdent -> WCM Bool
isQualConsId qid = gets (isCons qid)

shadows :: QualIdent -> WcState -> Maybe Ident
shadows qid s = do
  guard $ not (qualInLocalNestEnv qid sc)
  info      <- listToMaybe $ qualLookupNestEnv qid sc
  getVariable info
  where sc = scope s

importShadows :: QualIdent -> WcState -> Maybe Ident
importShadows qid s = do
  guard $ not (qualInLocalNestEnv qid sc)
  let qids = allBoundQualIdents $ valueEnv s
  listToMaybe $ map unqualify $ filter isMatchingImport qids
  where sc = scope s
        isMatchingImport qid' = unqualify qid' == unqualify qid
                             && isJust (qidModule qid')
                             && qidModule qid' /= Just (moduleId s)

shadowsVar :: Ident -> WCM (Maybe Ident)
shadowsVar v = gets (shadows $ commonId v)

shadowsImport :: Ident -> WCM (Maybe Ident)
shadowsImport v = gets (importShadows $ commonId v)

visitId :: Ident -> WCM ()
visitId v = modifyScope (qualModifyNestEnv visitVariable (commonId v))

visitQId :: QualIdent -> WCM ()
visitQId v = do
  mid <- getModuleIdent
  maybe ok visitId (localIdent mid v)

visitTypeId :: Ident -> WCM ()
visitTypeId v = modifyScope (qualModifyNestEnv visitVariable (typeId v))

visitQTypeId :: QualIdent -> WCM ()
visitQTypeId v = do
  mid <- getModuleIdent
  maybe ok visitTypeId (localIdent mid v)

isKnownVar :: Ident -> WCM Bool
isKnownVar v = gets $ \s -> isKnown s (commonId v)

isUnrefTypeVar :: Ident -> WCM Bool
isUnrefTypeVar v = gets (\s -> isUnref s (typeId v))

returnUnrefVars :: WCM [Ident]
returnUnrefVars = gets (\s ->
  let ids    = map fst (localNestEnv (scope s))
      unrefs = filter (isUnref s . qualify) ids
  in  unrefs )

inNestedScope :: WCM a -> WCM ()
inNestedScope m = beginScope >> m >> endScope

beginScope :: WCM ()
beginScope = modifyScope nestEnv

endScope :: WCM ()
endScope = modifyScope unnestEnv

------------------------------------------------------------------------------

isKnown :: WcState -> QualIdent -> Bool
isKnown s qid = qualInLocalNestEnv qid (scope s)

isUnref :: WcState -> QualIdent -> Bool
isUnref s qid = let sc = scope s
                in  any (not . variableVisited) (qualLookupNestEnv qid sc)
                    && qualInLocalNestEnv qid sc

isVar :: QualIdent -> WcState -> Bool
isVar qid s = maybe (isAnonId (unqualify qid))
                    isVariable
                    (listToMaybe (qualLookupNestEnv qid (scope s)))

isCons :: QualIdent -> WcState -> Bool
isCons qid s = maybe (isImportedCons s qid)
                      isConstructor
                      (listToMaybe (qualLookupNestEnv qid (scope s)))
 where isImportedCons s' qid' = case qualLookupValue qid' (valueEnv s') of
          (DataConstructor  _ _ _ _) : _ -> True
          (NewtypeConstructor _ _ _) : _ -> True
          _                              -> False

-- Since type identifiers and normal identifiers (e.g. functions, variables
-- or constructors) don't share the same namespace, it is necessary
-- to distinguish them in the scope environment of the check state.
-- For this reason type identifiers are annotated with 1 and normal
-- identifiers are annotated with 0.
commonId :: Ident -> QualIdent
commonId = qualify . unRenameIdent

typeId :: Ident -> QualIdent
typeId = qualify . flip renameIdent 1


-- --------------------------------------------------------------------------
-- Check Case Mode
-- --------------------------------------------------------------------------


-- The following functions traverse the AST and search for (defining)
-- identifiers and check if their names have the appropriate case mode.
checkCaseMode :: [Decl a] -> WCM ()
checkCaseMode = warnFor WarnIrregularCaseMode . mapM_ checkCaseModeDecl

checkCaseModeDecl :: Decl a -> WCM ()
checkCaseModeDecl (DataDecl _ tc vs cs _) = do
  checkCaseModeID isDataDeclName tc
  mapM_ (checkCaseModeID isVarName) vs
  mapM_ checkCaseModeConstr cs
checkCaseModeDecl (NewtypeDecl _ tc vs nc _) = do
  checkCaseModeID isDataDeclName tc
  mapM_ (checkCaseModeID isVarName) vs
  checkCaseModeNewConstr nc
checkCaseModeDecl (TypeDecl _ tc vs ty) = do
  checkCaseModeID isDataDeclName tc
  mapM_ (checkCaseModeID isVarName) vs
  checkCaseModeTypeExpr ty
checkCaseModeDecl (TypeSig _ fs qty) = do
  mapM_ (checkCaseModeID isFuncName) fs
  checkCaseModeQualTypeExpr qty
checkCaseModeDecl (FunctionDecl _ _ f eqs) = do
  checkCaseModeID isFuncName f
  mapM_ checkCaseModeEquation eqs
checkCaseModeDecl (ExternalDecl _ vs) =
  mapM_ (checkCaseModeID isFuncName . varIdent) vs
checkCaseModeDecl (PatternDecl _ t rhs) = do
  checkCaseModePattern t
  checkCaseModeRhs rhs
checkCaseModeDecl (FreeDecl  _ vs) =
  mapM_ (checkCaseModeID isVarName . varIdent) vs
checkCaseModeDecl (DefaultDecl _ tys) = mapM_ checkTypeExpr tys
checkCaseModeDecl (ClassDecl _ _ cx cls tv ds) = do
  checkCaseModeContext cx
  checkCaseModeID isClassDeclName cls
  checkCaseModeID isVarName tv
  mapM_ checkCaseModeDecl ds
checkCaseModeDecl (InstanceDecl _ _ cx _ inst ds) = do
  checkCaseModeContext cx
  checkCaseModeTypeExpr inst
  mapM_ checkCaseModeDecl ds
checkCaseModeDecl (DetSig _ fs dty) = do
  mapM_ (checkCaseModeID isFuncName) fs
  checkCaseModeDetExpr dty
checkCaseModeDecl _ = ok

checkCaseModeConstr :: ConstrDecl -> WCM ()
checkCaseModeConstr (ConstrDecl _ c tys) = do
  checkCaseModeID isConstrName c
  mapM_ checkCaseModeTypeExpr tys
checkCaseModeConstr (ConOpDecl  _ ty1 c ty2) = do
  checkCaseModeTypeExpr ty1
  checkCaseModeID isConstrName c
  checkCaseModeTypeExpr ty2
checkCaseModeConstr (RecordDecl _ c fs) = do
  checkCaseModeID isConstrName c
  mapM_ checkCaseModeFieldDecl fs

checkCaseModeFieldDecl :: FieldDecl -> WCM ()
checkCaseModeFieldDecl (FieldDecl _ fs ty) = do
  mapM_ (checkCaseModeID isFuncName) fs
  checkCaseModeTypeExpr ty

checkCaseModeNewConstr :: NewConstrDecl -> WCM ()
checkCaseModeNewConstr (NewConstrDecl _ nc ty) = do
  checkCaseModeID isConstrName nc
  checkCaseModeTypeExpr ty
checkCaseModeNewConstr (NewRecordDecl _ nc (f, ty)) = do
  checkCaseModeID isConstrName nc
  checkCaseModeID isFuncName f
  checkCaseModeTypeExpr ty

checkCaseModeContext :: Context -> WCM ()
checkCaseModeContext = mapM_ checkCaseModeConstraint

checkCaseModeConstraint :: Constraint -> WCM ()
checkCaseModeConstraint (Constraint _ _ ty) = checkCaseModeTypeExpr ty

checkCaseModeTypeExpr :: TypeExpr -> WCM ()
checkCaseModeTypeExpr (ApplyType _ ty1 ty2) = do
  checkCaseModeTypeExpr ty1
  checkCaseModeTypeExpr ty2
checkCaseModeTypeExpr (VariableType _ tv) = checkCaseModeID isVarName tv
checkCaseModeTypeExpr (TupleType _ tys) = mapM_ checkCaseModeTypeExpr tys
checkCaseModeTypeExpr (ListType _ ty) = checkCaseModeTypeExpr ty
checkCaseModeTypeExpr (ArrowType _ ty1 ty2) = do
  checkCaseModeTypeExpr ty1
  checkCaseModeTypeExpr ty2
checkCaseModeTypeExpr (ParenType _ ty) = checkCaseModeTypeExpr ty
checkCaseModeTypeExpr (ForallType _ tvs ty) = do
  mapM_ (checkCaseModeID isVarName) tvs
  checkCaseModeTypeExpr ty
checkCaseModeTypeExpr _ = ok

checkCaseModeQualTypeExpr :: QualTypeExpr -> WCM ()
checkCaseModeQualTypeExpr (QualTypeExpr _ cx ty) = do
  checkCaseModeContext cx
  checkCaseModeTypeExpr ty

checkCaseModeDetExpr :: DetExpr -> WCM ()
checkCaseModeDetExpr (DetDetExpr _) = ok
checkCaseModeDetExpr (AnyDetExpr _) = ok
checkCaseModeDetExpr (ParenDetExpr _ dty) =
  checkCaseModeDetExpr dty
checkCaseModeDetExpr (VarDetExpr _ v) =
  checkCaseModeID isVarName v
checkCaseModeDetExpr (ArrowDetExpr _ dty1 dty2) =
  checkCaseModeDetExpr dty1 >> checkCaseModeDetExpr dty2

checkCaseModeEquation :: Equation a -> WCM ()
checkCaseModeEquation (Equation _ lhs rhs) = do
  checkCaseModeLhs lhs
  checkCaseModeRhs rhs

checkCaseModeLhs :: Lhs a -> WCM ()
checkCaseModeLhs (FunLhs _ f ts) = do
  checkCaseModeID isFuncName f
  mapM_ checkCaseModePattern ts
checkCaseModeLhs (OpLhs _ t1 f t2) = do
  checkCaseModePattern t1
  checkCaseModeID isFuncName f
  checkCaseModePattern t2
checkCaseModeLhs (ApLhs _ lhs ts) = do
  checkCaseModeLhs lhs
  mapM_ checkCaseModePattern ts

checkCaseModeRhs :: Rhs a -> WCM ()
checkCaseModeRhs (SimpleRhs _ _ e ds) = do
  checkCaseModeExpr e
  mapM_ checkCaseModeDecl ds
checkCaseModeRhs (GuardedRhs _ _ es ds) = do
  mapM_ checkCaseModeCondExpr es
  mapM_ checkCaseModeDecl ds

checkCaseModeCondExpr :: CondExpr a -> WCM ()
checkCaseModeCondExpr (CondExpr _ g e) = do
  checkCaseModeExpr g
  checkCaseModeExpr e

checkCaseModePattern :: Pattern a -> WCM ()
checkCaseModePattern (VariablePattern _ _ v) = checkCaseModeID isVarName v
checkCaseModePattern (ConstructorPattern _ _ _ ts) =
  mapM_ checkCaseModePattern ts
checkCaseModePattern (InfixPattern _ _ t1 _ t2) = do
  checkCaseModePattern t1
  checkCaseModePattern t2
checkCaseModePattern (ParenPattern _ t) = checkCaseModePattern t
checkCaseModePattern (RecordPattern _ _ _ fs) =
  mapM_ checkCaseModeFieldPattern fs
checkCaseModePattern (TuplePattern _ ts) = mapM_ checkCaseModePattern ts
checkCaseModePattern (ListPattern _ _ ts) = mapM_ checkCaseModePattern ts
checkCaseModePattern (AsPattern _ v t) = do
  checkCaseModeID isVarName v
  checkCaseModePattern t
checkCaseModePattern (LazyPattern _ t) = checkCaseModePattern t
checkCaseModePattern (FunctionPattern _ _ _ ts) = mapM_ checkCaseModePattern ts
checkCaseModePattern (InfixFuncPattern _ _ t1 _ t2) = do
  checkCaseModePattern t1
  checkCaseModePattern t2
checkCaseModePattern _ = ok

checkCaseModeExpr :: Expression a -> WCM ()
checkCaseModeExpr (Paren _ e) = checkCaseModeExpr e
checkCaseModeExpr (Typed _ e qty) = do
  checkCaseModeExpr e
  checkCaseModeQualTypeExpr qty
checkCaseModeExpr (Record _ _ _ fs) = mapM_ checkCaseModeFieldExpr fs
checkCaseModeExpr (RecordUpdate _ e fs) = do
  checkCaseModeExpr e
  mapM_ checkCaseModeFieldExpr fs
checkCaseModeExpr (Tuple _ es) = mapM_ checkCaseModeExpr es
checkCaseModeExpr (List _ _ es) = mapM_ checkCaseModeExpr es
checkCaseModeExpr (ListCompr _ e stms)  = do
  checkCaseModeExpr e
  mapM_ checkCaseModeStatement stms
checkCaseModeExpr (EnumFrom _ e) = checkCaseModeExpr e
checkCaseModeExpr (EnumFromThen _ e1 e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (EnumFromTo _ e1 e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (EnumFromThenTo _ e1 e2 e3) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
  checkCaseModeExpr e3
checkCaseModeExpr (UnaryMinus _ e) = checkCaseModeExpr e
checkCaseModeExpr (Apply _ e1 e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (InfixApply _ e1 _ e2) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
checkCaseModeExpr (LeftSection _ e _) = checkCaseModeExpr e
checkCaseModeExpr (RightSection _ _ e) = checkCaseModeExpr e
checkCaseModeExpr (Lambda _ ts e) = do
  mapM_ checkCaseModePattern ts
  checkCaseModeExpr e
checkCaseModeExpr (Let _ _ ds e) = do
  mapM_ checkCaseModeDecl ds
  checkCaseModeExpr e
checkCaseModeExpr (Do _ _ stms e) = do
  mapM_ checkCaseModeStatement stms
  checkCaseModeExpr e
checkCaseModeExpr (IfThenElse _ e1 e2 e3) = do
  checkCaseModeExpr e1
  checkCaseModeExpr e2
  checkCaseModeExpr e3
checkCaseModeExpr (Case _ _ _ e as) = do
  mapM_ checkCaseModeAlt as
  checkCaseModeExpr e
checkCaseModeExpr _ = ok

checkCaseModeStatement :: Statement a -> WCM ()
checkCaseModeStatement (StmtExpr _    e) = checkCaseModeExpr e
checkCaseModeStatement (StmtDecl _ _ ds) = mapM_ checkCaseModeDecl ds
checkCaseModeStatement (StmtBind _  t e) = do
  checkCaseModePattern t
  checkCaseModeExpr e

checkCaseModeAlt :: Alt a -> WCM ()
checkCaseModeAlt (Alt _ t rhs) = checkCaseModePattern t >> checkCaseModeRhs rhs

checkCaseModeFieldPattern :: Field (Pattern a) -> WCM ()
checkCaseModeFieldPattern (Field _ _ t) = checkCaseModePattern t

checkCaseModeFieldExpr :: Field (Expression a) -> WCM ()
checkCaseModeFieldExpr (Field _ _ e) = checkCaseModeExpr e

checkCaseModeID :: (CaseMode -> String -> Bool) -> Ident -> WCM ()
checkCaseModeID f i@(Ident _ name _) = do
  c <- gets caseMode
  unless (f c name) (report $ warnCaseMode i c)

isVarName :: CaseMode -> String -> Bool
isVarName CaseModeProlog  (x:_) | isAlpha x = isUpper x
isVarName CaseModeGoedel  (x:_) | isAlpha x = isLower x
isVarName CaseModeHaskell (x:_) | isAlpha x = isLower x
isVarName _               _     = True

isFuncName :: CaseMode -> String -> Bool
isFuncName CaseModeHaskell (x:_) | isAlpha x = isLower x
isFuncName CaseModeGoedel  (x:_) | isAlpha x = isUpper x
isFuncName CaseModeProlog  (x:_) | isAlpha x = isLower x
isFuncName _               _     = True

isConstrName :: CaseMode -> String -> Bool
isConstrName = isDataDeclName

isClassDeclName :: CaseMode -> String -> Bool
isClassDeclName = isDataDeclName

isDataDeclName :: CaseMode -> String -> Bool
isDataDeclName CaseModeProlog  (x:_) | isAlpha x = isLower x
isDataDeclName CaseModeGoedel  (x:_) | isAlpha x = isUpper x
isDataDeclName CaseModeHaskell (x:_) | isAlpha x = isUpper x
isDataDeclName _               _     = True

-- ---------------------------------------------------------------------------
-- Warn for redundant context
-- ---------------------------------------------------------------------------

--traverse the AST for QualTypeExpr/Context and check for redundancy
checkRedContext :: [Decl a] -> WCM ()
checkRedContext = warnFor WarnRedundantContext . mapM_ checkRedContextDecl

getRedPredSet :: ModuleIdent -> ClassEnv -> TCEnv -> PredSet -> PredSet
getRedPredSet m cenv tcEnv ps =
  Set.map (pm Map.!) $ Set.difference qps $ minPredSet cenv qps --or fromJust $ Map.lookup
  where (qps, pm) = Set.foldr qualifyAndAddPred (Set.empty, Map.empty) ps
        qualifyAndAddPred p@(Pred qid ty) (ps', pm') =
          let qp = Pred (getOrigName m qid tcEnv) ty
          in (Set.insert qp ps', Map.insert qp p pm')

getPredFromContext :: Context -> ([Ident], PredSet)
getPredFromContext cx =
  let vs = concatMap (\(Constraint _ _ ty) -> typeVariables ty) cx
  in (vs, toPredSet vs cx)

checkRedContext' :: (Pred -> Message) -> PredSet -> WCM ()
checkRedContext' f ps = do
  m     <- gets moduleId
  cenv  <- gets classEnv
  tcEnv <- gets tyConsEnv
  mapM_ (report . f) (getRedPredSet m cenv tcEnv ps)

checkRedContextDecl :: Decl a -> WCM ()
checkRedContextDecl (TypeSig _ ids (QualTypeExpr _ cx _)) =
  checkRedContext' (warnRedContext (warnRedFuncString ids) vs) ps
  where (vs, ps) = getPredFromContext cx
checkRedContextDecl (FunctionDecl _ _ _ eqs) = mapM_ checkRedContextEq eqs
checkRedContextDecl (PatternDecl _ _ rhs) = checkRedContextRhs rhs
checkRedContextDecl (ClassDecl _ _ cx i _ ds) = do
  checkRedContext'
    (warnRedContext (text ("class declaration " ++ escName i)) vs)
    ps
  mapM_ checkRedContextDecl ds
  where (vs, ps) = getPredFromContext cx
checkRedContextDecl (InstanceDecl _ _ cx qid _ ds) = do
  checkRedContext'
    (warnRedContext (text ("instance declaration " ++ escQualName qid)) vs)
    ps
  mapM_ checkRedContextDecl ds
  where (vs, ps) = getPredFromContext cx
checkRedContextDecl _ = return ()

checkRedContextEq :: Equation a -> WCM ()
checkRedContextEq (Equation _ _ rhs) = checkRedContextRhs rhs

checkRedContextRhs :: Rhs a -> WCM ()
checkRedContextRhs (SimpleRhs  _ _ e  ds) = do
  checkRedContextExpr e
  mapM_ checkRedContextDecl ds
checkRedContextRhs (GuardedRhs _ _ cs ds) = do
  mapM_ checkRedContextCond cs
  mapM_ checkRedContextDecl ds

checkRedContextCond :: CondExpr a -> WCM ()
checkRedContextCond (CondExpr _ e1 e2) = do
  checkRedContextExpr e1
  checkRedContextExpr e2

checkRedContextExpr :: Expression a -> WCM ()
checkRedContextExpr (Paren _ e) = checkRedContextExpr e
checkRedContextExpr (Typed _ e (QualTypeExpr _ cx _)) = do
  checkRedContextExpr e
  checkRedContext' (warnRedContext (text "type signature") vs) ps
  where (vs, ps) = getPredFromContext cx
checkRedContextExpr (Record _ _ _ fs) = mapM_ checkRedContextFieldExpr fs
checkRedContextExpr (RecordUpdate _ e fs) = do
  checkRedContextExpr e
  mapM_ checkRedContextFieldExpr fs
checkRedContextExpr (Tuple  _ es) = mapM_ checkRedContextExpr es
checkRedContextExpr (List _ _ es) = mapM_ checkRedContextExpr es
checkRedContextExpr (ListCompr _ e sts) = do
  checkRedContextExpr e
  mapM_ checkRedContextStmt sts
checkRedContextExpr (EnumFrom _ e) = checkRedContextExpr e
checkRedContextExpr (EnumFromThen _ e1 e2) = do
  checkRedContextExpr e1
  checkRedContextExpr e2
checkRedContextExpr (EnumFromTo _ e1 e2) = do
  checkRedContextExpr e1
  checkRedContextExpr e2
checkRedContextExpr (EnumFromThenTo _ e1 e2 e3) = do
  checkRedContextExpr e1
  checkRedContextExpr e2
  checkRedContextExpr e3
checkRedContextExpr (UnaryMinus _ e) = checkRedContextExpr e
checkRedContextExpr (Apply _ e1 e2) = do
  checkRedContextExpr e1
  checkRedContextExpr e2
checkRedContextExpr (InfixApply _ e1 _ e2) = do
  checkRedContextExpr e1
  checkRedContextExpr e2
checkRedContextExpr (LeftSection  _ e _) = checkRedContextExpr e
checkRedContextExpr (RightSection _ _ e) = checkRedContextExpr e
checkRedContextExpr (Lambda _ _ e) = checkRedContextExpr e
checkRedContextExpr (Let _ _ ds e) = do
  mapM_ checkRedContextDecl ds
  checkRedContextExpr e
checkRedContextExpr (IfThenElse _ e1 e2 e3) = do
  checkRedContextExpr e1
  checkRedContextExpr e2
  checkRedContextExpr e3
checkRedContextExpr (Case _ _ _ e as) = do
  checkRedContextExpr e
  mapM_ checkRedContextAlt as
checkRedContextExpr _ = return ()

checkRedContextStmt :: Statement a -> WCM ()
checkRedContextStmt (StmtExpr   _  e) = checkRedContextExpr e
checkRedContextStmt (StmtDecl _ _ ds) = mapM_ checkRedContextDecl ds
checkRedContextStmt (StmtBind _ _  e) = checkRedContextExpr e

checkRedContextAlt :: Alt a -> WCM ()
checkRedContextAlt (Alt _ _ rhs) = checkRedContextRhs rhs

checkRedContextFieldExpr :: Field (Expression a) -> WCM ()
checkRedContextFieldExpr (Field _ _ e) = checkRedContextExpr e

-- ---------------------------------------------------------------------------
-- Check that IO is used deterministically
-- ---------------------------------------------------------------------------

-- We use MaybeT to olny throw the innermost warning for each declaration.
checkDeterministicIO :: [Decl (PredType, DetType)] -> WCM ()
checkDeterministicIO = warnFor WarnNondeterministicIO .
  mapM_ (runMaybeT . checkDeterministicIODecl)

type CheckIO = MaybeT WCM

checkDeterministicIODecl :: Decl (PredType, DetType) -> CheckIO ()
checkDeterministicIODecl (FunctionDecl _ _ _ eqs) =
  mapM_ checkDeterministicIOEq eqs
checkDeterministicIODecl (PatternDecl _ _ rhs) =
  checkDeterministicIORhs rhs
checkDeterministicIODecl (ClassDecl _ _ _ _ _ ds) =
  mapM_ checkDeterministicIODecl ds
checkDeterministicIODecl (InstanceDecl _ _ _ _ _ ds) =
  mapM_ checkDeterministicIODecl ds
checkDeterministicIODecl _ = return ()

checkDeterministicIOEq :: Equation (PredType, DetType) -> CheckIO ()
checkDeterministicIOEq (Equation _ _ rhs) = checkDeterministicIORhs rhs

checkDeterministicIORhs :: Rhs (PredType, DetType) -> CheckIO ()
checkDeterministicIORhs (SimpleRhs  _ _ e  ds) = do
  checkDeterministicIOExpr e
  mapM_ checkDeterministicIODecl ds
checkDeterministicIORhs (GuardedRhs _ _ cs ds) = do
  mapM_ checkDeterministicIOCond cs
  mapM_ checkDeterministicIODecl ds

checkDeterministicIOCond :: CondExpr (PredType, DetType) -> CheckIO ()
checkDeterministicIOCond (CondExpr _ e1 e2) = do
  checkDeterministicIOExpr e1
  checkDeterministicIOExpr e2

checkDeterministicIOExpr :: Expression (PredType, DetType) -> CheckIO ()
checkDeterministicIOExpr (Paren _ e) =
  checkDeterministicIOExpr e
checkDeterministicIOExpr (Typed _ e _) =
  checkDeterministicIOExpr e
checkDeterministicIOExpr (Record _ _ _ fs) =
  mapM_ checkDeterministicIOFieldExpr fs
checkDeterministicIOExpr (RecordUpdate _ e fs) = do
  checkDeterministicIOExpr e
  mapM_ checkDeterministicIOFieldExpr fs
checkDeterministicIOExpr (Tuple  _ es) =
  mapM_ checkDeterministicIOExpr es
checkDeterministicIOExpr (List _ _ es) =
  mapM_ checkDeterministicIOExpr es
checkDeterministicIOExpr (ListCompr _ e sts) = do
  checkDeterministicIOExpr e
  mapM_ checkDeterministicIOStmt sts
checkDeterministicIOExpr (EnumFrom _ e) =
  checkDeterministicIOExpr e
checkDeterministicIOExpr (EnumFromThen _ e1 e2) = do
  checkDeterministicIOExpr e1
  checkDeterministicIOExpr e2
checkDeterministicIOExpr (EnumFromTo _ e1 e2) = do
  checkDeterministicIOExpr e1
  checkDeterministicIOExpr e2
checkDeterministicIOExpr (EnumFromThenTo _ e1 e2 e3) = do
  checkDeterministicIOExpr e1
  checkDeterministicIOExpr e2
  checkDeterministicIOExpr e3
checkDeterministicIOExpr (UnaryMinus _ e) =
  checkDeterministicIOExpr e
checkDeterministicIOExpr e@(Apply spi e1 e2) = do
  checkDeterministicIOExpr e1
  checkDeterministicIOExpr e2
  let (PredType _ ty1', _) = bothTypesOf e1
      (PredType _ _, dty) = bothTypesOf e
      ty1 = ty1'
  when (checkNDIOType ty1 dty) $ liftAndAbort $
    report $ warnNondeterministicIO spi "application"
checkDeterministicIOExpr e@(InfixApply spi e1 op e2) = do
  checkDeterministicIOExpr e1
  checkDeterministicIOExpr e2
  let (PredType _ ty1', _) = bothTypesOf op
      (PredType _ _, dty) = bothTypesOf e
      ty1 =ty1'
  when (checkNDIOType ty1 dty) $ liftAndAbort $
    report $ warnNondeterministicIO spi "infix application"
checkDeterministicIOExpr e@(LeftSection spi e' op) = do
  checkDeterministicIOExpr e'
  let (PredType _ ty1', _) = bothTypesOf op
      (PredType _ _, dty) = bothTypesOf e
      ty1 = ty1'
  when (checkNDIOType ty1 dty) $ liftAndAbort $
    report $ warnNondeterministicIO spi "left section"
checkDeterministicIOExpr e@(RightSection spi op e') = do
  checkDeterministicIOExpr e'
  let (PredType _ ty1', _) = bothTypesOf op
      (PredType _ _, dty) = bothTypesOf e
      ty1 = ty1'
  when (checkNDIOType ty1 dty) $ liftAndAbort $
    report $ warnNondeterministicIO spi "right section"
checkDeterministicIOExpr (Lambda _ _ e) =
  checkDeterministicIOExpr e
checkDeterministicIOExpr (Let _ _ ds e) = do
  mapM_ checkDeterministicIODecl ds
  checkDeterministicIOExpr e
checkDeterministicIOExpr (IfThenElse _ e1 e2 e3) = do
  checkDeterministicIOExpr e1
  checkDeterministicIOExpr e2
  checkDeterministicIOExpr e3
checkDeterministicIOExpr (Case _ _ _ e as) = do
  checkDeterministicIOExpr e
  mapM_ checkDeterministicIOAlt as
checkDeterministicIOExpr (Do _ _ stms e) = do
  mapM_ checkDeterministicIOStmt stms
  checkDeterministicIOExpr e
checkDeterministicIOExpr Literal {} = ok
checkDeterministicIOExpr Constructor {} = ok
checkDeterministicIOExpr Variable {} = ok

checkDeterministicIOStmt :: Statement (PredType, DetType) -> CheckIO ()
checkDeterministicIOStmt (StmtExpr   _  e) = checkDeterministicIOExpr e
checkDeterministicIOStmt (StmtDecl _ _ ds) = mapM_ checkDeterministicIODecl ds
checkDeterministicIOStmt (StmtBind _ _ e) = checkDeterministicIOExpr e

checkDeterministicIOAlt :: Alt (PredType, DetType) -> CheckIO ()
checkDeterministicIOAlt (Alt _ _ rhs) = checkDeterministicIORhs rhs

checkDeterministicIOFieldExpr :: Field (Expression (PredType, DetType)) -> CheckIO ()
checkDeterministicIOFieldExpr (Field _ _ e) = checkDeterministicIOExpr e

liftAndAbort :: WCM () -> CheckIO ()
liftAndAbort wcm = MaybeT $ do
  wcm
  return Nothing

-- When the function returns something in IO and
-- the result of this application is nondeterministic,
-- then we generate a warning.
{-# INLINE checkNDIOType #-}
checkNDIOType :: Type -> DetType -> Bool
checkNDIOType ty1 resdty =
  rootOfTypeMaybe (snd (arrowUnapply ty1)) == Just qIOId &&
  snd (arrowUnapplyDetType resdty) == Any

class BothTypesOf a where
  bothTypesOf :: a -> (PredType, DetType)

instance BothTypesOf (PredType, DetType) where
  bothTypesOf = id

{-# SPECIALISE bothTypesOf :: Expression (PredType, DetType) #-}
instance BothTypesOf a => BothTypesOf (Expression a) where
  bothTypesOf (Variable _ a _) = bothTypesOf a
  bothTypesOf (Constructor _ a _) = bothTypesOf a
  bothTypesOf (Paren _ e) = bothTypesOf e
  bothTypesOf (Literal _ a _) = bothTypesOf a
  bothTypesOf (Typed _ e _) = bothTypesOf e
  bothTypesOf (Tuple _ es) =
    let (ptys, dtys) = unzip $ map bothTypesOf es
        (pss, tys) = unzip $ map (\(PredType ps ty) -> (ps, ty)) ptys
    in (PredType (Set.unions pss) (mkTupleTy tys), head dtys)
  bothTypesOf (List _ a _) = bothTypesOf a
  bothTypesOf (UnaryMinus _ e) = bothTypesOf e
  bothTypesOf (Record _ a _ _) = bothTypesOf a
  bothTypesOf (RecordUpdate _ e _) = bothTypesOf e
  bothTypesOf (Do _ _ _ e) = bothTypesOf e
  bothTypesOf (IfThenElse _ _ e _) = bothTypesOf e
  bothTypesOf (Let _ _ _ e) = bothTypesOf e
  bothTypesOf (Case _ _ _ _ alts) = bothTypesOf $ head alts
  bothTypesOf (ListCompr _ e _) =
    let (PredType ps ty, dty) = bothTypesOf e
    in (PredType ps (listType ty), dty)
  bothTypesOf (EnumFrom _ e) =
    let (PredType ps ty, dty) = bothTypesOf e
    in (PredType ps (listType ty), dty)
  bothTypesOf (EnumFromThen _ e _) =
    let (PredType ps ty, dty) = bothTypesOf e
    in (PredType ps (listType ty), dty)
  bothTypesOf (EnumFromTo _ e _) =
    let (PredType ps ty, dty) = bothTypesOf e
    in (PredType ps (listType ty), dty)
  bothTypesOf (EnumFromThenTo _ e _ _) =
    let (PredType ps ty, dty) = bothTypesOf e
    in (PredType ps (listType ty), dty)
  bothTypesOf (Lambda _ pats e) =
    let (ptys, dtys) = unzip $ map bothTypesOf pats
        (PredType eps ety, edty) = bothTypesOf e
        (pss, tys) = unzip $ map (\(PredType ps ty) -> (ps, ty)) ptys
        ty' = foldr TypeArrow ety tys
        dty' = foldr DetArrow edty dtys
    in (PredType (Set.unions (eps:pss)) ty', dty')
  bothTypesOf (LeftSection _ e op) =
    let (PredType eps _, edty) = bothTypesOf e
        (PredType ops oty, odty) = bothTypesOf op
        ty' = case oty of
          TypeArrow _ ty -> ty
          _ -> internalError $ "WarnCheck.bothTypesOf.LeftSection: " ++ show oty
        dty' = applyDetType odty [edty]
    in (PredType (Set.union eps ops) ty', dty')
  bothTypesOf (RightSection _ op e) =
    let (PredType eps _, edty) = bothTypesOf e
        (PredType ops oty, odty) = bothTypesOf op
        ty' = case oty of
          TypeArrow ty1 (TypeArrow _ ty2) -> TypeArrow ty1 ty2
          _ -> internalError $ "WarnCheck.bothTypesOf.RightSection: " ++ show oty
        dty' = case odty of
          DetArrow dty1 dty2 -> DetArrow dty1 (applyDetType dty2 [edty])
          VarTy _ -> Det
          Det -> Det
          Any -> Any
    in (PredType (Set.union eps ops) ty', dty')
  bothTypesOf (Apply _ e1 e2) =
    let (PredType e1ps e1ty, e1dty) = bothTypesOf e1
        (PredType e2ps _, e2dty) = bothTypesOf e2
        ty' = case e1ty of
          TypeArrow _ ty -> ty
          _ -> internalError $ "WarnCheck.bothTypesOf.Apply: " ++ show e1ty
        dty' = applyDetType e1dty [e2dty]
    in (PredType (Set.union e1ps e2ps) ty', dty')
  bothTypesOf (InfixApply _ e1 op e2) =
    let (PredType e1ps _, e1dty) = bothTypesOf e1
        (PredType e2ps _, e2dty) = bothTypesOf e2
        (PredType ops opty, opdty) = bothTypesOf op
        ty' = case opty of
          TypeArrow _ (TypeArrow _ ty) -> ty
          _ -> internalError $ "WarnCheck.bothTypesOf.InfixApply: " ++ show opty
        dty' = applyDetType opdty [e1dty, e2dty]
    in (PredType (Set.union e1ps (Set.union e2ps ops)) ty', dty')

instance BothTypesOf a => BothTypesOf (InfixOp a) where
  bothTypesOf (InfixConstr a _) = bothTypesOf a
  bothTypesOf (InfixOp a _) = bothTypesOf a

instance BothTypesOf a => BothTypesOf (Pattern a) where
  bothTypesOf (VariablePattern _ a _) = bothTypesOf a
  bothTypesOf (LiteralPattern _ a _) = bothTypesOf a
  bothTypesOf (NegativePattern _ a _) = bothTypesOf a
  bothTypesOf (ConstructorPattern _ a _ _) = bothTypesOf a
  bothTypesOf (InfixPattern _ a _ _ _) = bothTypesOf a
  bothTypesOf (RecordPattern _ a _ _) = bothTypesOf a
  bothTypesOf (ListPattern _ a _) = bothTypesOf a
  bothTypesOf (InfixFuncPattern _ a _ _ _) = bothTypesOf a
  bothTypesOf (FunctionPattern _ a _ _) = bothTypesOf a
  bothTypesOf (ParenPattern _ p) = bothTypesOf p
  bothTypesOf (AsPattern _ _ p) = bothTypesOf p
  bothTypesOf (LazyPattern _ p) = bothTypesOf p
  bothTypesOf (TuplePattern _ pats) =
    let (ptys, dtys) = unzip $ map bothTypesOf pats
        (pss, tys) = unzip $ map (\(PredType ps ty) -> (ps, ty)) ptys
    in (PredType (Set.unions pss) (mkTupleTy tys), head dtys)

instance BothTypesOf a => BothTypesOf (Alt a) where
  bothTypesOf (Alt _ _ rhs) = bothTypesOf rhs

instance BothTypesOf a => BothTypesOf (Rhs a) where
  bothTypesOf (SimpleRhs _ _ e _) = bothTypesOf e
  bothTypesOf (GuardedRhs _ _ gs _) = bothTypesOf $ head gs

instance BothTypesOf a => BothTypesOf (CondExpr a) where
  bothTypesOf (CondExpr _ _ e) = bothTypesOf e

mkTupleTy :: [Type] -> Type
mkTupleTy xs = foldr TypeApply (TypeConstructor (qTupleId (length xs))) xs

arrowUnapplyDetType :: DetType -> ([DetType], DetType)
arrowUnapplyDetType (DetArrow ty1 ty2) =
  let (tys, res) = arrowUnapplyDetType ty2
  in (ty1:tys, res)
arrowUnapplyDetType ty = ([], ty)

-- ---------------------------------------------------------------------------
-- Warning messages
-- ---------------------------------------------------------------------------

warnNondeterministicIO :: SpanInfo -> String -> Message
warnNondeterministicIO spi s = spanInfoMessage spi $
  text "Potentially nondeterministic use of I/O in" <+> text s
  $+$ text "Consider encapsulating the offending sub-expressssion"
  $+$ text "or add a determinism signature to the applied function"

warnRedFuncString :: [Ident] -> Doc
warnRedFuncString is = text "type signature for function" <>
                       text (if length is == 1 then [] else "s") <+>
                       csep (map (text . escName) is)

-- Doc description -> TypeVars -> Pred -> Warning
warnRedContext :: Doc -> [Ident] -> Pred -> Message
warnRedContext d vs p@(Pred qid _) = spanInfoMessage qid $
  text "Redundant context in" <+> d <> colon <+>
  quotes (pPrint $ fromPred vs p) -- idents use ` ' as quotes not ' '

-- seperate a list by ', '
csep :: [Doc] -> Doc
csep []     = empty
csep [x]    = x
csep (x:xs) = x <> comma <+> csep xs

warnCaseMode :: Ident -> CaseMode -> Message
warnCaseMode i@(Ident _ name _ ) c = spanInfoMessage i $
  text "Wrong case mode in symbol" <+> text (escName i) <+>
  text "due to selected case mode" <+> text (escapeCaseMode c) <> comma <+>
  text "try renaming to" <+> text (caseSuggestion name) <+> text "instead"

caseSuggestion :: String -> String
caseSuggestion (x:xs) | isLower x = toUpper x : xs
                      | isUpper x = toLower x : xs
caseSuggestion _      = internalError
 "Checks.WarnCheck.caseSuggestion: Identifier starts with illegal Symbol"

escapeCaseMode :: CaseMode -> String
escapeCaseMode CaseModeFree    = "`free`"
escapeCaseMode CaseModeHaskell = "`haskell`"
escapeCaseMode CaseModeProlog  = "`prolog`"
escapeCaseMode CaseModeGoedel  = "`goedel`"

warnUnrefTypeVar :: Ident -> Message
warnUnrefTypeVar v = spanInfoMessage v $ hsep $ map text
  [ "Unreferenced type variable", escName v ]

warnUnrefVar :: Ident -> Message
warnUnrefVar v = spanInfoMessage v $ hsep $ map text
  [ "Unused declaration of variable", escName v ]

warnShadowing :: Ident -> Ident -> Message
warnShadowing x v = spanInfoMessage x $
  text "Shadowing symbol" <+> text (escName x)
  <> comma <+> text "bound at:" <+> ppPosition (getPosition v)
