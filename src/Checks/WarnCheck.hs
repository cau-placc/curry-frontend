{- |
    Module      :  $Header$
    Description :  Checks for irregular code
    Copyright   :  (c) 2006        Martin Engelke
                       2011 - 2014 Björn Peemöller
                       2014 - 2015 Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module searches for potentially irregular code and generates
    warning messages.
-}

{-# LANGUAGE CPP #-}
module Checks.WarnCheck (warnCheck) where

#if __GLASGOW_HASKELL__ >= 804
import Prelude hiding ((<>))
#endif

import           Control.Monad
  (filterM, foldM_, guard, liftM, liftM2, when, unless)
import           Control.Monad.State.Strict    (State, execState, gets, modify)
import qualified Data.IntSet         as IntSet
  (IntSet, empty, insert, notMember, singleton, union, unions)
import qualified Data.Map            as Map    (empty, insert, lookup)
import           Data.Maybe
  (catMaybes, fromMaybe, listToMaybe)
import           Data.List
  (intersect, intersectBy, nub, sort, unionBy)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty (ppPattern, ppExpr, ppIdent)

import Base.CurryTypes (ppTypeScheme)
import Base.Messages   (Message, posMessage, internalError)
import Base.NestEnv    ( NestEnv, emptyEnv, localNestEnv, nestEnv, unnestEnv
                       , qualBindNestEnv, qualInLocalNestEnv, qualLookupNestEnv
                       , qualModifyNestEnv)

import Base.Types
import Base.Utils (findMultiples)
import Env.ModuleAlias
import Env.TypeConstructor (TCEnv, TypeInfo (..), lookupTC, qualLookupTC)
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
warnCheck :: WarnOpts -> AliasEnv -> ValueEnv -> TCEnv -> Module -> [Message]
warnCheck opts aEnv valEnv tcEnv (Module _ mid es is ds)
  = runOn (initWcState mid aEnv valEnv tcEnv (wnWarnFlags opts)) $ do
      checkImports   is
      checkDeclGroup ds
      checkExports   es
      checkMissingTypeSignatures ds
      checkModuleAlias is

type ScopeEnv = NestEnv IdInfo

-- Current state of generating warnings
data WcState = WcState
  { moduleId    :: ModuleIdent
  , scope       :: ScopeEnv
  , aliasEnv    :: AliasEnv
  , valueEnv    :: ValueEnv
  , tyConsEnv   :: TCEnv
  , warnFlags   :: [WarnFlag]
  , warnings    :: [Message]
  }

-- The monadic representation of the state allows the usage of monadic
-- syntax (do expression) for dealing easier and safer with its
-- contents.
type WCM = State WcState

initWcState :: ModuleIdent -> AliasEnv -> ValueEnv -> TCEnv -> [WarnFlag]
            -> WcState
initWcState mid ae ve te wf = WcState mid emptyEnv ae ve te wf []

getModuleIdent :: WCM ModuleIdent
getModuleIdent = gets moduleId

modifyScope :: (ScopeEnv -> ScopeEnv) -> WCM ()
modifyScope f = modify $ \s -> s { scope = f $ scope s }

warnFor :: WarnFlag -> WCM () -> WCM ()
warnFor f act = do
  warn <- gets $ \s -> f `elem` warnFlags s
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

ok :: WCM ()
ok = return ()

-- |Run a 'WCM' action and return the list of messages
runOn :: WcState -> WCM a -> [Message]
runOn s f = sort $ warnings $ execState f s

-- ---------------------------------------------------------------------------
-- checkExports
-- ---------------------------------------------------------------------------

checkExports :: Maybe ExportSpec -> WCM () -- TODO checks
checkExports Nothing                      = ok
checkExports (Just (Exporting _ exports)) = do
  mapM_ visitExport exports
  reportUnusedGlobalVars
    where
      visitExport (Export qid) = visitQId qid
      visitExport _            = ok

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
        mapM_ (report . (warnMultiplyImportedSymbol mid) . impName) iis
        setImportSpec env mid (unionBy cmpImport is' is, hs)
    where iis = intersectBy cmpImport is' is

  checkImportSpec env _ mid (is, hs) (Just (Hiding _ hs'))
    | null ihs  = setImportSpec env mid (is, hs' ++ hs)
    | otherwise = do
        mapM_ (report . (warnMultiplyHiddenSymbol mid) . impName) ihs
        setImportSpec env mid (is, unionBy cmpImport hs' hs)
    where ihs = intersectBy cmpImport hs' hs

  fromImpSpec Nothing                 = ([], [])
  fromImpSpec (Just (Importing _ is)) = (is, [])
  fromImpSpec (Just (Hiding    _ hs)) = ([], hs)

  setImportSpec env mid ishs = return $ Map.insert mid ishs env

  cmpImport (ImportTypeWith id1 cs1) (ImportTypeWith id2 cs2)
    = id1 == id2 && null (intersect cs1 cs2)
  cmpImport i1 i2 = (impName i1) == (impName i2)

  impName (Import           v) = v
  impName (ImportTypeAll    t) = t
  impName (ImportTypeWith t _) = t

warnMultiplyImportedModule :: ModuleIdent -> Message
warnMultiplyImportedModule mid = posMessage mid $ hsep $ map text
  ["Module", moduleName mid, "is imported more than once"]

warnMultiplyImportedSymbol :: ModuleIdent -> Ident -> Message
warnMultiplyImportedSymbol mid ident = posMessage ident $ hsep $ map text
  [ "Symbol", escName ident, "from module", moduleName mid
  , "is imported more than once" ]

warnMultiplyHiddenSymbol :: ModuleIdent -> Ident -> Message
warnMultiplyHiddenSymbol mid ident = posMessage ident $ hsep $ map text
  [ "Symbol", escName ident, "from module", moduleName mid
  , "is hidden more than once" ]

-- ---------------------------------------------------------------------------
-- checkDeclGroup
-- ---------------------------------------------------------------------------

checkDeclGroup :: [Decl] -> WCM ()
checkDeclGroup ds = do
  mapM_ insertDecl   ds
  mapM_ checkDecl    ds
  checkRuleAdjacency ds

checkLocalDeclGroup :: [Decl] -> WCM ()
checkLocalDeclGroup ds = do
  mapM_ checkLocalDecl ds
  checkDeclGroup       ds

-- ---------------------------------------------------------------------------
-- Find function rules which are disjoined
-- ---------------------------------------------------------------------------

checkRuleAdjacency :: [Decl] -> WCM ()
checkRuleAdjacency decls = warnFor WarnDisjoinedRules
                         $ foldM_ check (mkIdent "", Map.empty) decls
  where
  check (prevId, env) (FunctionDecl p f _) = do
    cons <- isConsId f
    if cons || prevId == f
      then return (f, env)
      else case Map.lookup f env of
        Nothing -> return (f, Map.insert f p env)
        Just p' -> do
          report $ warnDisjoinedFunctionRules f p'
          return (f, env)
  check (_    , env) _                     = return (mkIdent "", env)

warnDisjoinedFunctionRules :: Ident -> Position -> Message
warnDisjoinedFunctionRules ident pos = posMessage ident $ hsep (map text
  [ "Rules for function", escName ident, "are disjoined" ])
  <+> parens (text "first occurrence at" <+> text (showLine pos))

checkDecl :: Decl -> WCM ()
checkDecl (DataDecl   _ _ vs cs) = inNestedScope $ do
  mapM_ insertTypeVar   vs
  mapM_ checkConstrDecl cs
  reportUnusedTypeVars  vs
checkDecl (TypeDecl   _ _ vs ty) = inNestedScope $ do
  mapM_ insertTypeVar  vs
  checkTypeExpr ty
  reportUnusedTypeVars vs
checkDecl (FunctionDecl p f eqs) = checkFunctionDecl p f eqs
checkDecl (PatternDecl  _ p rhs) = checkPattern p >> checkRhs rhs
checkDecl _                      = ok

checkConstrDecl :: ConstrDecl -> WCM ()
checkConstrDecl (ConstrDecl     _ _ c tys) = do
  visitId c
  mapM_ checkTypeExpr tys
checkConstrDecl (ConOpDecl _ _ ty1 op ty2) = do
  visitId op
  mapM_ checkTypeExpr [ty1, ty2]
checkConstrDecl (RecordDecl _ _ c fs) = do
  visitId c
  mapM_ checkTypeExpr tys
  where
    tys = [ty | FieldDecl _ _ ty <- fs]

checkTypeExpr :: TypeExpr -> WCM ()
checkTypeExpr (ConstructorType qid tys) = do
  visitQTypeId qid
  mapM_ checkTypeExpr tys
checkTypeExpr (VariableType          v) = visitTypeId v
checkTypeExpr (TupleType           tys) = mapM_ checkTypeExpr tys
checkTypeExpr (ListType             ty) = checkTypeExpr ty
checkTypeExpr (ArrowType       ty1 ty2) = mapM_ checkTypeExpr [ty1, ty2]
checkTypeExpr (ParenType            ty) = checkTypeExpr ty

-- Checks locally declared identifiers (i.e. functions and logic variables)
-- for shadowing
checkLocalDecl :: Decl -> WCM ()
checkLocalDecl (FunctionDecl _ f _) = checkShadowing f
checkLocalDecl (FreeDecl      _ vs) = mapM_ checkShadowing vs
checkLocalDecl (PatternDecl  _ p _) = checkPattern p
checkLocalDecl _                    = ok

checkFunctionDecl :: Position -> Ident -> [Equation] -> WCM ()
checkFunctionDecl _ _ []  = ok
checkFunctionDecl p f eqs = inNestedScope $ do
  mapM_ checkEquation eqs
  checkFunctionPatternMatch p f eqs

checkFunctionPatternMatch :: Position -> Ident -> [Equation] -> WCM ()
checkFunctionPatternMatch p f eqs = do
  let pats = map (\(Equation _ lhs _) -> snd (flatLhs lhs)) eqs
  (nonExhaustive, overlapped, nondet) <- checkPatternMatching pats
  unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
    warnMissingPattern p ("an equation for " ++ escName f) nonExhaustive
  when (nondet || not (null overlapped)) $ warnFor WarnOverlapping $ report $
    warnNondetOverlapping p ("Function " ++ escName f)

-- Check an equation for warnings.
-- This is done in a seperate scope as the left-hand-side may introduce
-- new variables.
checkEquation :: Equation -> WCM ()
checkEquation (Equation _ lhs rhs) = inNestedScope $ do
  checkLhs lhs
  checkRhs rhs
  reportUnusedVars

checkLhs :: Lhs -> WCM ()
checkLhs (FunLhs    _ ts) = do
  mapM_ checkPattern ts
  mapM_ (insertPattern False) ts
checkLhs (OpLhs t1 op t2) = checkLhs (FunLhs op [t1, t2])
checkLhs (ApLhs   lhs ts) = do
  checkLhs lhs
  mapM_ checkPattern ts
  mapM_ (insertPattern False) ts

checkPattern :: Pattern -> WCM ()
checkPattern (VariablePattern        v) = checkShadowing v
checkPattern (ConstructorPattern  _ ps) = mapM_ checkPattern ps
checkPattern (InfixPattern     p1 f p2) = checkPattern
                                          (ConstructorPattern f [p1, p2])
checkPattern (ParenPattern           p) = checkPattern p
checkPattern (RecordPattern       _ fs) = mapM_ (checkField checkPattern) fs
checkPattern (TuplePattern        _ ps) = mapM_ checkPattern ps
checkPattern (ListPattern         _ ps) = mapM_ checkPattern ps
checkPattern (AsPattern            v p) = checkShadowing v >> checkPattern p
checkPattern (LazyPattern          _ p) = checkPattern p
checkPattern (FunctionPattern     _ ps) = mapM_ checkPattern ps
checkPattern (InfixFuncPattern p1 f p2) = checkPattern
                                          (FunctionPattern f [p1, p2])
checkPattern _                          = ok

-- Check the right-hand-side of an equation.
-- Because local declarations may introduce new variables, we need
-- another scope nesting.
checkRhs :: Rhs -> WCM ()
checkRhs (SimpleRhs _ e ds) = inNestedScope $ do
  checkLocalDeclGroup ds
  checkExpr e
  reportUnusedVars
checkRhs (GuardedRhs ce ds) = inNestedScope $ do
  checkLocalDeclGroup ds
  mapM_ checkCondExpr ce
  reportUnusedVars

checkCondExpr :: CondExpr -> WCM ()
checkCondExpr (CondExpr _ c e) = checkExpr c >> checkExpr e

checkExpr :: Expression -> WCM ()
checkExpr (Variable              v) = visitQId v
checkExpr (Paren                 e) = checkExpr e
checkExpr (Typed               e _) = checkExpr e
checkExpr (Record             _ fs) = mapM_ (checkField checkExpr) fs
checkExpr (RecordUpdate       e fs) = do
  checkExpr e
  mapM_ (checkField checkExpr) fs
checkExpr (Tuple              _ es) = mapM_ checkExpr es
checkExpr (List               _ es) = mapM_ checkExpr es
checkExpr (ListCompr       _ e sts) = checkStatements sts e
checkExpr (EnumFrom              e) = checkExpr e
checkExpr (EnumFromThen      e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (EnumFromTo        e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (EnumFromThenTo e1 e2 e3) = mapM_ checkExpr [e1, e2, e3]
checkExpr (UnaryMinus          _ e) = checkExpr e
checkExpr (Apply             e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (InfixApply     e1 op e2) = do
  visitQId (opName op)
  mapM_ checkExpr [e1, e2]
checkExpr (LeftSection         e _) = checkExpr e
checkExpr (RightSection        _ e) = checkExpr e
checkExpr (Lambda           _ ps e) = inNestedScope $ do
  mapM_ checkPattern ps
  mapM_ (insertPattern False) ps
  checkExpr e
  reportUnusedVars
checkExpr (Let                ds e) = inNestedScope $ do
  checkLocalDeclGroup ds
  checkExpr e
  reportUnusedVars
checkExpr (Do                sts e) = checkStatements sts e
checkExpr (IfThenElse   _ e1 e2 e3) = mapM_ checkExpr [e1, e2, e3]
checkExpr (Case        _ ct e alts) = do
  checkExpr e
  mapM_ checkAlt alts
  checkCaseAlts ct alts
checkExpr _                       = ok

checkStatements :: [Statement] -> Expression -> WCM ()
checkStatements []     e = checkExpr e
checkStatements (s:ss) e = inNestedScope $ do
  checkStatement s >> checkStatements ss e
  reportUnusedVars

checkStatement :: Statement -> WCM ()
checkStatement (StmtExpr   _ e) = checkExpr e
checkStatement (StmtDecl    ds) = checkLocalDeclGroup ds
checkStatement (StmtBind _ p e) = do
  checkPattern p >> insertPattern False p
  checkExpr e

checkAlt :: Alt -> WCM ()
checkAlt (Alt _ p rhs) = inNestedScope $ do
  checkPattern p >> insertPattern False p
  checkRhs rhs
  reportUnusedVars

checkField :: (a -> WCM ()) -> Field a -> WCM ()
checkField check (Field _ _ x) = check x

-- -----------------------------------------------------------------------------
-- Check for missing type signatures
-- -----------------------------------------------------------------------------

-- |Check if every top-level function has an accompanying type signature.
-- For external function declarations, this check is already performed
-- during syntax checking.
checkMissingTypeSignatures :: [Decl] -> WCM ()
checkMissingTypeSignatures ds = warnFor WarnMissingSignatures $ do
  let typedFs   = [f | TypeSig     _ fs _ <- ds, f <- fs]
      untypedFs = [f | FunctionDecl _ f _ <- ds, f `notElem` typedFs]
  unless (null untypedFs) $ do
    mid   <- getModuleIdent
    tyScs <- mapM getTyScheme untypedFs
    mapM_ report $ zipWith (warnMissingTypeSignature mid) untypedFs tyScs

getTyScheme :: Ident -> WCM TypeScheme
getTyScheme q = do
  m     <- getModuleIdent
  tyEnv <- gets valueEnv
  return $ case qualLookupValue (qualifyWith m q) tyEnv of
    [Value  _ _ tys] -> tys
    _                -> internalError $
      "Checks.WarnCheck.getTyScheme: " ++ show q

warnMissingTypeSignature :: ModuleIdent -> Ident -> TypeScheme -> Message
warnMissingTypeSignature mid i tys = posMessage i $ fsep
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
warnModuleNameClash mid = posMessage mid $ hsep $ map text
  ["The module alias", escModuleName mid
  , "overlaps with the current module name"]

warnAliasNameClash :: [ModuleIdent] -> Message
warnAliasNameClash []         = internalError
  "WarnCheck.warnAliasNameClash: empty list"
warnAliasNameClash mids = posMessage (head mids) $ text
  "Overlapping module aliases" $+$ nest 2 (vcat (map myppAlias mids))
  where myppAlias mid@(ModuleIdent pos _) =
          ppLine pos <> text ":" <+> text (escModuleName mid)

-- -----------------------------------------------------------------------------
-- Check for overlapping/unreachable and non-exhaustive case alternatives
-- -----------------------------------------------------------------------------

checkCaseAlts :: CaseType -> [Alt] -> WCM ()
checkCaseAlts _  []                   = ok
checkCaseAlts ct alts@(Alt p _ _ : _) = do
  let pats = map (\(Alt _ pat _) -> [pat]) alts
  (nonExhaustive, overlapped, nondet) <- checkPatternMatching pats
  case ct of
    Flex -> do
      unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
        warnMissingPattern p "an fcase alternative" nonExhaustive
      when (nondet || not (null overlapped)) $ warnFor WarnOverlapping $ report
        $ warnNondetOverlapping p "An fcase expression"
    Rigid -> do
      unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
        warnMissingPattern p "a case alternative" nonExhaustive
      unless (null overlapped) $ warnFor WarnOverlapping $ report $
        warnUnreachablePattern p overlapped

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

checkPatternMatching :: [[Pattern]] -> WCM ([ExhaustivePats], [[Pattern]], Bool)
checkPatternMatching pats = do
  -- 1. We simplify the patterns by removing syntactic sugar temporarily
  --    for a simpler implementation.
  simplePats <- mapM (mapM simplifyPat) pats
  -- 2. We compute missing and used pattern matching alternatives
  (missing, used, nondet) <- processEqs (zip [1..] simplePats)
  -- 3. If any, we report the missing patterns, whereby we re-add the syntactic
  --    sugar removed in step (1) for a more precise output.
  nonExhaustive <- mapM tidyExhaustivePats missing
  let overlap = [ eqn | (i, eqn) <- zip [1..] pats, i `IntSet.notMember` used]
  return (nonExhaustive , overlap, nondet)

-- |Simplify a 'Pattern' until it only consists of
--   * Variables
--   * Integer, Float or Char literals
--   * Constructors
-- All other patterns like as-patterns, list patterns and alike are desugared.
simplifyPat :: Pattern -> WCM Pattern
simplifyPat p@(LiteralPattern      l) = return $ case l of
  String r s -> simplifyListPattern $ map (LiteralPattern . Char r) s
  _          -> p
simplifyPat (NegativePattern     _ l) = return $ LiteralPattern (negateLit l)
  where
  negateLit (Int   i n) = Int   i (-n)
  negateLit (Float r d) = Float r (-d)
  negateLit x           = x
simplifyPat v@(VariablePattern     _) = return v
simplifyPat (ConstructorPattern c ps) = ConstructorPattern c `liftM`
                                        mapM simplifyPat ps
simplifyPat (InfixPattern    p1 c p2) = ConstructorPattern c `liftM`
                                        mapM simplifyPat [p1, p2]
simplifyPat (ParenPattern          p) = simplifyPat p
simplifyPat (RecordPattern      c fs) = do
  (_, ls) <- getAllLabels c
  let ps = map (getPattern (map field2Tuple fs)) ls
  simplifyPat (ConstructorPattern c ps)
  where
    getPattern fs' l' = fromMaybe (VariablePattern anonId)
                                  (lookup l' [(unqualify l, p) | (l, p) <- fs'])
simplifyPat (TuplePattern       _ ps)
  | null ps   = return $ ConstructorPattern qUnitId []
  | otherwise = ConstructorPattern (qTupleId (length ps))
                `liftM` mapM simplifyPat ps
simplifyPat (ListPattern        _ ps) = simplifyListPattern `liftM`
                                        mapM simplifyPat ps
simplifyPat (AsPattern           _ p) = simplifyPat p
simplifyPat (LazyPattern         _ _) = return $ VariablePattern anonId
simplifyPat (FunctionPattern     _ _) = return $ VariablePattern anonId
simplifyPat (InfixFuncPattern  _ _ _) = return $ VariablePattern anonId

getAllLabels :: QualIdent -> WCM (QualIdent, [Ident])
getAllLabels c = do
  tyEnv <- gets valueEnv
  case qualLookupValue c tyEnv of
    [DataConstructor qc _ ls _] -> return (qc, ls)
    _                           -> internalError $
          "Checks.WarnCheck.getAllLabels: " ++ show c

-- |Create a simplified list pattern by applying @:@ and @[]@.
simplifyListPattern :: [Pattern] -> Pattern
simplifyListPattern = foldr (\p1 p2 -> ConstructorPattern qConsId [p1, p2])
                                      (ConstructorPattern qNilId [])

-- |'ExhaustivePats' describes those pattern missing for an exhaustive
-- pattern matching, where a value can be thought of as a missing equation.
-- The first component contains the unmatched patterns, while the second
-- pattern contains an identifier and the literals matched for this identifier.
--
-- This is necessary when checking literal patterns because of the sheer
-- number of possible patterns. Missing literals are therefore converted
-- into the form @ ... x ... with x `notElem` [l1, ..., ln]@.
type EqnPats = [Pattern]
type EqnNo   = Int
type EqnInfo = (EqnNo, EqnPats)

type ExhaustivePats = (EqnPats, [(Ident, [Literal])])
type EqnSet  = IntSet.IntSet

-- |Compute the missing pattern by inspecting the first patterns and
-- categorize them as literal, constructor or variable patterns.
processEqs :: [EqnInfo] -> WCM ([ExhaustivePats], EqnSet, Bool)
processEqs []              = return ([], IntSet.empty, False)
processEqs eqs@((n, ps):_)
  | null ps                    = return ([], IntSet.singleton n, length eqs > 1)
  | any isLitPat firstPats     = processLits eqs
  | any isConPat firstPats     = processCons eqs
  | all isVarPat firstPats     = processVars eqs
  | otherwise                  = internalError "Checks.WarnCheck.processEqs"
  where firstPats = map firstPat eqs

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
  defaultPat = ( VariablePattern newVar : replicate (length (snd q) - 1) wildPat
               , [(newVar, usedLits)])
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
    return (map (\(xs, ys) -> (LiteralPattern lit : xs, ys)) missing, used, nd && ovlp)

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
  defaultPat c = (mkPattern c : replicate (length (snd q) - 1) wildPat, [])
  mkPattern  c = ConstructorPattern
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
                   in ConstructorPattern c args : rest

  removeFirstCon c a (n, p:ps)
    | isVarPat p = (n, replicate a wildPat ++ ps)
    | isCon c  p = (n, patArgs p           ++ ps)
  removeFirstCon _ _ _ = internalError "Checks.WarnCheck.removeFirstCon"

-- |Variable patterns are exhaustive, so they are checked by simply
-- checking the following patterns.
processVars :: [EqnInfo] -> WCM ([ExhaustivePats], EqnSet, Bool)
processVars []               = error "WarnCheck.processVars"
processVars eqs@((n, _) : _) = do
  let ovlp = length eqs > 1
  (missing, used, nd) <- processEqs (map shiftPat eqs)
  return ( map (\(xs, ys) -> (wildPat : xs, ys)) missing
         , IntSet.insert n used, nd && ovlp)

-- |Return the constructors of a type not contained in the list of constructors.
getUnusedCons :: [QualIdent] -> WCM [DataConstr]
getUnusedCons []       = internalError "Checks.WarnCheck.getUnusedCons"
getUnusedCons qs@(q:_) = do
  allCons <- getConTy q >>= getTyCons q . arrowBase
  return [ c | c <- allCons, (constrIdent c) `notElem` map unqualify qs]

-- |Retrieve the type of a given constructor.
getConTy :: QualIdent -> WCM Type
getConTy q = do
  tyEnv <- gets valueEnv
  tcEnv <- gets tyConsEnv
  case qualLookupValue q tyEnv of
    [DataConstructor  _ _ _ (ForAllExist _ _ ty)] -> return ty
    [NewtypeConstructor _ _ (ForAllExist _ _ ty)] -> return ty
    _                                           -> case qualLookupTC q tcEnv of
      [AliasType _ _ ty] -> return ty
      _                  -> internalError $
        "Checks.WarnCheck.getConTy: " ++ show q

-- |Retrieve all constructors of a given type.
getTyCons :: QualIdent -> Type -> WCM [DataConstr]
getTyCons _ (TypeConstructor tc _) = do
  tc'   <- unAlias tc
  tcEnv <- gets tyConsEnv
  return $ case lookupTC (unqualify tc) tcEnv of
    [DataType     _ _ cs] -> cs
    [RenamingType _ _ nc] -> [nc]
    _ -> case qualLookupTC tc' tcEnv of
      [DataType     _ _ cs] -> cs
      [RenamingType _ _ nc] -> [nc]
      err                   -> internalError $ "Checks.WarnCheck.getTyCons: "
                            ++ show tc ++ ' ' : show err ++ '\n' : show tcEnv
getTyCons _ _ = internalError "Checks.WarnCheck.getTyCons"

-- |Resugar the exhaustive patterns previously desugared at 'simplifyPat'.
tidyExhaustivePats :: ExhaustivePats -> WCM ExhaustivePats
tidyExhaustivePats (xs, ys) = mapM tidyPat xs >>= \xs' -> return (xs', ys)

-- |Resugar a pattern previously desugared at 'simplifyPat', i.e.
--   * Convert a tuple constructor pattern into a tuple pattern
--   * Convert a list constructor pattern representing a finite list
--     into a list pattern
tidyPat :: Pattern -> WCM Pattern
tidyPat p@(LiteralPattern        _) = return p
tidyPat p@(VariablePattern       _) = return p
tidyPat p@(ConstructorPattern c ps)
  | c == qUnitId && null ps         = return $ TuplePattern noRef []
  | isQTupleId c                    = TuplePattern noRef `liftM` mapM tidyPat ps
  | c == qConsId && isFiniteList p  = ListPattern []     `liftM`
                                      mapM tidyPat (unwrapFinite p)
  | c == qConsId                    = unwrapInfinite p
  | otherwise                       = ConstructorPattern c `liftM` mapM tidyPat ps
  where
  isFiniteList (ConstructorPattern d []     )                = d == qNilId
  isFiniteList (ConstructorPattern d [_, e2]) | d == qConsId = isFiniteList e2
  isFiniteList _                                             = False

  unwrapFinite (ConstructorPattern _ []     ) = []
  unwrapFinite (ConstructorPattern _ [p1,p2]) = p1 : unwrapFinite p2
  unwrapFinite pat
    = internalError $ "WarnCheck.tidyPat.unwrapFinite: " ++ show pat

  unwrapInfinite (ConstructorPattern d [p1,p2]) = liftM2 (flip InfixPattern d)
                                                  (tidyPat p1)
                                                  (unwrapInfinite p2)
  unwrapInfinite p0                             = return p0

tidyPat p = internalError $ "Checks.WarnCheck.tidyPat: " ++ show p

-- |Get the first pattern of a list.
firstPat :: EqnInfo -> Pattern
firstPat (_, []   ) = internalError "Checks.WarnCheck.firstPat: empty list"
firstPat (_, (p:_)) = p

-- |Drop the first pattern of a list.
shiftPat :: EqnInfo -> EqnInfo
shiftPat (_, []    ) = internalError "Checks.WarnCheck.shiftPat: empty list"
shiftPat (n, (_:ps)) = (n, ps)

-- |Wildcard pattern.
wildPat :: Pattern
wildPat = VariablePattern anonId

-- |Retrieve any literal out of a pattern.
getLit :: Pattern -> [Literal]
getLit (LiteralPattern l) = [l]
getLit _                  = []

-- |Retrieve the constructor name and its arity for a pattern.
getCon :: Pattern -> [(QualIdent, Int)]
getCon (ConstructorPattern c ps) = [(c, length ps)]
getCon _                         = []

-- |Is a pattern a variable or literal pattern?
isVarLit :: Literal -> Pattern -> Bool
isVarLit l p = isVarPat p || isLit l p

-- |Is a pattern a variable or a constructor pattern with the given constructor?
isVarCon :: QualIdent -> Pattern -> Bool
isVarCon c p = isVarPat p || isCon c p

-- |Is a pattern a pattern matching for the given constructor?
isCon :: QualIdent -> Pattern -> Bool
isCon c (ConstructorPattern d _) = c == d
isCon _ _                        = False

-- |Is a pattern a pattern matching for the given literal?
isLit :: Literal -> Pattern -> Bool
isLit l (LiteralPattern m) = l == m
isLit _ _                  = False

-- |Is a pattern a literal pattern?
isLitPat :: Pattern -> Bool
isLitPat (LiteralPattern  _) = True
isLitPat _                   = False

-- |Is a pattern a variable pattern?
isVarPat :: Pattern -> Bool
isVarPat (VariablePattern _) = True
isVarPat _                   = False

-- |Is a pattern a constructor pattern?
isConPat :: Pattern -> Bool
isConPat (ConstructorPattern _ _) = True
isConPat      _                   = False

-- |Retrieve the arguments of a pattern.
patArgs :: Pattern -> [Pattern]
patArgs (ConstructorPattern _ ps) = ps
patArgs _                         = []

-- |Warning message for non-exhaustive patterns.
-- To shorten the output only the first 'maxPattern' are printed,
-- additional pattern are abbreviated by dots.
warnMissingPattern :: Position -> String -> [ExhaustivePats] -> Message
warnMissingPattern p loc pats = posMessage p
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
    where ppPats = hsep (map (ppPattern 2) ps)
  ppCons (i, lits) = ppIdent i <+> text "`notElem`"
                 <+> ppExpr 0 (List [] (map Literal lits))

-- |Warning message for unreachable patterns.
-- To shorten the output only the first 'maxPattern' are printed,
-- additional pattern are abbreviated by dots.
warnUnreachablePattern :: Position  -> [[Pattern]] -> Message
warnUnreachablePattern p pats = posMessage p
  $   text "Pattern matches are unreachable"
  $+$ text "In a case alternative:"
  $+$ nest 2 (vcat (ppExPats pats) <+> text "->" <+> text "...")
  where
  ppExPats ps
    | length ps > maxPattern = ppPats ++ [text "..."]
    | otherwise              = ppPats
    where ppPats = map ppPat (take maxPattern ps)
  ppPat ps = hsep (map (ppPattern 2) ps)

-- |Maximum number of missing patterns to be shown.
maxPattern :: Int
maxPattern = 4

warnNondetOverlapping :: Position -> String -> Message
warnNondetOverlapping p loc = posMessage p $
  text loc <+> text "is non-deterministic due to overlapping rules"

-- -----------------------------------------------------------------------------

checkShadowing :: Ident -> WCM ()
checkShadowing x = warnFor WarnNameShadowing $
  shadowsVar x >>= maybe ok (report . warnShadowing x)

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

insertDecl :: Decl -> WCM ()
insertDecl (DataDecl     _ d _ cs) = do
  insertTypeConsId d
  mapM_ insertConstrDecl cs
insertDecl (TypeDecl     _ t _ ty) = do
  insertTypeConsId t
  insertTypeExpr ty
insertDecl (FunctionDecl    _ f _) = do
  cons <- isConsId f
  unless cons $ insertVar f
insertDecl (ForeignDecl _ _ _ f _) = insertVar f
insertDecl (ExternalDecl     _ vs) = mapM_ insertVar vs
insertDecl (PatternDecl     _ p _) = insertPattern False p
insertDecl (FreeDecl         _ vs) = mapM_ insertVar vs
insertDecl _                       = ok

insertTypeExpr :: TypeExpr -> WCM ()
insertTypeExpr (VariableType        _) = ok
insertTypeExpr (ConstructorType _ tys) = mapM_ insertTypeExpr tys
insertTypeExpr (TupleType         tys) = mapM_ insertTypeExpr tys
insertTypeExpr (ListType           ty) = insertTypeExpr ty
insertTypeExpr (ArrowType     ty1 ty2) = mapM_ insertTypeExpr [ty1,ty2]
insertTypeExpr (ParenType          ty) = insertTypeExpr ty

insertConstrDecl :: ConstrDecl -> WCM ()
insertConstrDecl (ConstrDecl _ _    c _) = insertConsId c
insertConstrDecl (ConOpDecl  _ _ _ op _) = insertConsId op
insertConstrDecl (RecordDecl _ _    c _) = insertConsId c

-- 'fp' indicates whether 'checkPattern' deals with the arguments
-- of a function pattern or not.
-- Since function patterns are not recognized before syntax check, it is
-- necessary to determine whether a constructor pattern represents a
-- constructor or a function.
insertPattern :: Bool -> Pattern -> WCM ()
insertPattern fp (VariablePattern        v) = do
  cons <- isConsId v
  unless cons $ do
    var <- isVarId v
    if and [fp, var, not (isAnonId v)] then visitId v else insertVar v
insertPattern fp (ConstructorPattern  c ps) = do
  cons <- isQualConsId c
  mapM_ (insertPattern (not cons || fp)) ps
insertPattern fp (InfixPattern p1 c p2)
  = insertPattern fp (ConstructorPattern c [p1, p2])
insertPattern fp (ParenPattern           p) = insertPattern fp p
insertPattern fp (RecordPattern       _ fs) = mapM_ (insertFieldPattern fp) fs
insertPattern fp (TuplePattern        _ ps) = mapM_ (insertPattern fp) ps
insertPattern fp (ListPattern         _ ps) = mapM_ (insertPattern fp) ps
insertPattern fp (AsPattern            v p) = insertVar v >> insertPattern fp p
insertPattern fp (LazyPattern          _ p) = insertPattern fp p
insertPattern _  (FunctionPattern     f ps) = do
  visitQId f
  mapM_ (insertPattern True) ps
insertPattern _  (InfixFuncPattern p1 f p2)
  = insertPattern True (FunctionPattern f [p1, p2])
insertPattern _ _ = ok

insertFieldPattern :: Bool -> Field Pattern -> WCM ()
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

shadowsVar :: Ident -> WCM (Maybe Ident)
shadowsVar v = gets (shadows $ commonId v)
  where
  shadows :: QualIdent -> WcState -> Maybe Ident
  shadows qid s = do
    guard $ not (qualInLocalNestEnv qid sc)
    info      <- listToMaybe $ qualLookupNestEnv qid sc
    getVariable info
    where sc = scope s

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
                in  (any (not . variableVisited) (qualLookupNestEnv qid sc))
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

-- ---------------------------------------------------------------------------
-- Warnings messages
-- ---------------------------------------------------------------------------

warnUnrefTypeVar :: Ident -> Message
warnUnrefTypeVar v = posMessage v $ hsep $ map text
  [ "Unreferenced type variable", escName v ]

warnUnrefVar :: Ident -> Message
warnUnrefVar v = posMessage v $ hsep $ map text
  [ "Unused declaration of variable", escName v ]

warnShadowing :: Ident -> Ident -> Message
warnShadowing x v = posMessage x $
  text "Shadowing symbol" <+> text (escName x)
  <> comma <+> text "bound at:" <+> ppPosition (getPosition v)
