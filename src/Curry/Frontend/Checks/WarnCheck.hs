{- |
    Module      :  $Header$
    Description :  Checks for irregular code
    Copyright   :  (c) 2006        Martin Engelke
                       2011 - 2014 Björn Peemöller
                       2014 - 2015 Jan Tikovsky
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module searches for potentially irregular code and generates
    warning messages.
-}
module Curry.Frontend.Checks.WarnCheck (warnCheck) where

import Prelude hiding ((<>))

import           Control.Monad
  (filterM, foldM_, guard, liftM2, when, unless, void)
import           Control.Monad.State.Strict    (State, execState, gets, modify)
import qualified Data.IntSet         as IntSet
  (IntSet, empty, insert, notMember, singleton, union, unions)
import           Data.Bifunctor
  (first)
import qualified Data.Map            as Map    (empty, insert, lookup, (!))
import qualified Data.Set            as Set
import           Data.Maybe
  (catMaybes, fromMaybe, listToMaybe, isJust)
import           Data.List
  ((\\), intersect, intersectBy, nub, sort, unionBy)
import           Data.Tuple.Extra
  (snd3)

import Curry.Base.Ident
import Curry.Base.Position ( Position, HasPosition(getPosition), ppPosition, ppLine, showLine, next)
import Curry.Base.Pretty
import Curry.Base.QuickFix ( QuickFix (..), prependFix, replaceFix, insertFix )
import Curry.Base.SpanInfo
import Curry.Syntax

import Curry.Frontend.Base.Messages   ( Message, spanInfoMessage, withFixes, internalError )
import Curry.Frontend.Base.NestEnv    ( NestEnv, emptyEnv, localNestEnv, nestEnv, unnestEnv
                                      , qualBindNestEnv, qualInLocalNestEnv, qualLookupNestEnv
                                      , qualModifyNestEnv)
import Curry.Frontend.Base.TopEnv     ( allBoundQualIdents )

import Curry.Frontend.Base.Types
import Curry.Frontend.Base.Utils      ( findMultiples )
import Curry.Frontend.Env.ModuleAlias ( AliasEnv )
import Curry.Frontend.Env.Class       ( ClassEnv, classMethods, hasDefaultImpl, minPredList )
import Curry.Frontend.Env.TypeConstructor
                                      ( TCEnv, TypeInfo (..), lookupTypeInfo
                                      , qualLookupTypeInfo, getOrigName )
import Curry.Frontend.Env.Value       ( ValueEnv, ValueInfo (..), qualLookupValue )

import Curry.Frontend.CompilerOpts    ( WarnFlag(..), WarnOpts(..) )

-- Find potentially incorrect code in a Curry program and generate warnings
-- for the following issues:
--   - multiply imported modules, multiply imported/hidden values
--   - unreferenced variables
--   - shadowing variables
--   - idle case alternatives
--   - overlapping case alternatives
--   - non-adjacent function rules
--   - redundant context
warnCheck :: WarnOpts -> AliasEnv -> ValueEnv -> TCEnv -> ClassEnv
          -> Module a -> [Message]
warnCheck wOpts aEnv valEnv tcEnv clsEnv mdl
  = runOn (initWcState mid aEnv valEnv tcEnv clsEnv (wnWarnFlags wOpts)) $ do
      checkImports   is
      checkDeclGroup ds
      checkExports   es
      checkMissingTypeSignatures ds
      checkModuleAlias is
      checkRedContext ds
  where Module _ _ _ mid es is ds = void mdl

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
  , warnings    :: [Message]
  }

-- The monadic representation of the state allows the usage of monadic
-- syntax (do expression) for dealing easier and safer with its
-- contents.
type WCM = State WcState

initWcState :: ModuleIdent -> AliasEnv -> ValueEnv -> TCEnv -> ClassEnv
            -> [WarnFlag] -> WcState
initWcState mid ae ve te ce wf = WcState mid emptyEnv ae ve te ce wf []

getModuleIdent :: WCM ModuleIdent
getModuleIdent = gets moduleId

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

checkDeclGroup :: [Decl ()] -> WCM ()
checkDeclGroup ds = do
  mapM_ insertDecl   ds
  mapM_ checkDecl    ds
  checkRuleAdjacency ds

checkLocalDeclGroup :: [Decl ()] -> WCM ()
checkLocalDeclGroup ds = do
  mapM_ checkLocalDecl ds
  checkDeclGroup       ds

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

checkDecl :: Decl () -> WCM ()
checkDecl (DataDecl           _ _ vs cs _) = inNestedScope $ do
  mapM_ insertTypeVar   vs
  mapM_ checkConstrDecl cs
  reportUnusedTypeVars  vs
checkDecl (NewtypeDecl        _ _ vs nc _) = inNestedScope $ do
  mapM_ insertTypeVar   vs
  checkNewConstrDecl nc
  reportUnusedTypeVars vs
checkDecl (TypeDecl             _ _ vs ty) = inNestedScope $ do
  mapM_ insertTypeVar  vs
  checkTypeExpr ty
  reportUnusedTypeVars vs
checkDecl (FunctionDecl         p _ f eqs) = checkFunctionDecl p f eqs
checkDecl (PatternDecl            _ p rhs) = checkPattern p >> checkRhs rhs
checkDecl (DefaultDecl              _ tys) = mapM_ checkTypeExpr tys
checkDecl (ClassDecl       _ _ _ _ _ _ ds) = mapM_ checkDecl ds
checkDecl (InstanceDecl p _ cx cls tys ds) = do
  checkOrphanInstance p cx cls tys
  checkMissingMethodImplementations p cls ds
  mapM_ checkDecl ds
checkDecl _                             = ok

--TODO: shadowing and context etc.
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

checkFunctionDecl :: SpanInfo -> Ident -> [Equation ()] -> WCM ()
checkFunctionDecl _ _ []  = ok
checkFunctionDecl p f eqs = inNestedScope $ do
  mapM_ checkEquation eqs
  checkFunctionPatternMatch p f eqs

checkFunctionPatternMatch :: SpanInfo -> Ident -> [Equation ()] -> WCM ()
checkFunctionPatternMatch spi f eqs = do
  let pats = map (\(Equation _ _ lhs _) -> snd (flatLhs lhs)) eqs
  let guards = map eq2Guards eqs
  (nonExhaustive, overlapped, nondet) <- checkPatternMatching pats guards
  unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
    warnMissingPattern spi ("an equation for " ++ escName f) nonExhaustive
  when (nondet || not (null overlapped)) $ warnFor WarnOverlapping $ report $
    warnNondetOverlapping spi ("Function " ++ escName f)
  where eq2Guards :: Equation () -> [CondExpr ()]
        eq2Guards (Equation _ _ _ (GuardedRhs _ _ conds _)) = conds
        eq2Guards _ = []

-- Check an equation for warnings.
-- This is done in a seperate scope as the left-hand-side may introduce
-- new variables.
checkEquation :: Equation () -> WCM ()
checkEquation (Equation _ _ lhs rhs) = inNestedScope $ do
  checkLhs lhs
  checkRhs rhs
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
checkRhs :: Rhs () -> WCM ()
checkRhs (SimpleRhs _ _ e ds) = inNestedScope $ do
  checkLocalDeclGroup ds
  checkExpr e
  reportUnusedVars
checkRhs (GuardedRhs _ _ ce ds) = inNestedScope $ do
  checkLocalDeclGroup ds
  mapM_ checkCondExpr ce
  reportUnusedVars

checkCondExpr :: CondExpr () -> WCM ()
checkCondExpr (CondExpr _ c e) = checkExpr c >> checkExpr e

checkExpr :: Expression () -> WCM ()
checkExpr (Variable            _ _ v) = visitQId v
checkExpr (Paren                 _ e) = checkExpr e
checkExpr (Typed               _ e _) = checkExpr e
checkExpr (Record           s _ q fs) = do
  checkMissingFields s q fs
  mapM_ (checkField checkExpr) fs
checkExpr (RecordUpdate       _ e fs) = do
  checkExpr e
  mapM_ (checkField checkExpr) fs
checkExpr (Tuple                _ es) = mapM_ checkExpr es
checkExpr (List               _ _ es) = mapM_ checkExpr es
checkExpr (ListCompr         _ e sts) = checkStatements sts e
checkExpr (EnumFrom              _ e) = checkExpr e
checkExpr (EnumFromThen      _ e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (EnumFromTo        _ e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (EnumFromThenTo _ e1 e2 e3) = mapM_ checkExpr [e1, e2, e3]
checkExpr (UnaryMinus            _ e) = checkExpr e
checkExpr (Apply             _ e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (InfixApply     _ e1 op e2) = do
  visitQId (opName op)
  mapM_ checkExpr [e1, e2]
checkExpr (LeftSection         _ e _) = checkExpr e
checkExpr (RightSection        _ _ e) = checkExpr e
checkExpr (Lambda             _ ps e) = inNestedScope $ do
  mapM_ checkPattern ps
  mapM_ (insertPattern False) ps
  checkExpr e
  reportUnusedVars
checkExpr (Let              _ _ ds e) = inNestedScope $ do
  checkLocalDeclGroup ds
  checkExpr e
  reportUnusedVars
checkExpr (Do              _ _ sts e) = checkStatements sts e
checkExpr (IfThenElse     _ e1 e2 e3) = mapM_ checkExpr [e1, e2, e3]
checkExpr (Case      spi _ ct e alts) = do
  checkExpr e
  mapM_ checkAlt alts
  checkCaseAlts spi ct alts
checkExpr _                       = ok

checkStatements :: [Statement ()] -> Expression () -> WCM ()
checkStatements []     e = checkExpr e
checkStatements (s:ss) e = inNestedScope $ do
  checkStatement s >> checkStatements ss e
  reportUnusedVars

checkStatement :: Statement () -> WCM ()
checkStatement (StmtExpr    _ e) = checkExpr e
checkStatement (StmtDecl _ _ ds) = checkLocalDeclGroup ds
checkStatement (StmtBind _  p e) = do
  checkPattern p >> insertPattern False p
  checkExpr e

checkAlt :: Alt () -> WCM ()
checkAlt (Alt _ p rhs) = inNestedScope $ do
  checkPattern p >> insertPattern False p
  checkRhs rhs
  reportUnusedVars

checkField :: (a -> WCM ()) -> Field a -> WCM ()
checkField check (Field _ _ x) = check x

-- -----------------------------------------------------------------------------
-- Check for missing record fields
-- -----------------------------------------------------------------------------

checkMissingFields :: SpanInfo -> QualIdent -> [Field (Expression ())] -> WCM ()
checkMissingFields spi q fs = warnFor WarnMissingFields $ do
  tyEnv <- gets valueEnv

  let idents = case qualLookupValue q tyEnv of
                 [DataConstructor  _ _ is _] -> is
                 [NewtypeConstructor _ i _]  -> [i]
                 _ -> internalError $ "Checks.WarnCheck.checkMissingFields: " ++ show q
      provided = Set.fromList $ map (\(Field _ fq _) -> idName (qidIdent fq)) fs
      missing  = filter (not . flip Set.member provided . idName) idents

  unless (null missing) $
    report (warnMissingFields spi q fs missing)

warnMissingFields :: SpanInfo -> QualIdent -> [Field (Expression ())] -> [Ident] -> Message
warnMissingFields spi q fs missing =
  withFixes [missingFieldsFix spi q fs missing] $
    spanInfoMessage spi $ fsep
      [ hsep $ map text ["Fields of", escName (qidIdent q), "not initialized and implicitly free:"]
        -- TODO: Provide the type here too, would require another lookup in checkMissingFields
      , nest 2 $ vcat $ map (text . showIdent) missing
      ]

missingFieldsFix :: SpanInfo -> QualIdent -> [Field (Expression ())] -> [Ident] -> QuickFix
missingFieldsFix spi q fs missing =
  insertFix
    insertPos
    (render (prefix <+> csep (map ((<+> text "= _") . text . showIdent) missing)))
    ("Make missing " ++ escName (qidIdent q) ++ " fields explicit")
  where prefix | null fs   = empty
               | otherwise = comma
        insertPos | null fs   = getSrcSpanEnd spi
                  | otherwise = case last fs of Field _ _ e -> next (getSrcSpanEnd e)

-- -----------------------------------------------------------------------------
-- Check for orphan instances
-- -----------------------------------------------------------------------------

checkOrphanInstance :: SpanInfo -> Context -> QualIdent -> [TypeExpr] -> WCM ()
checkOrphanInstance p cx cls tys = warnFor WarnOrphanInstances $ do
  m <- getModuleIdent
  tcEnv <- gets tyConsEnv
  let ocls = getOrigName m cls tcEnv
      otcs = map (flip (getOrigName m) tcEnv . typeConstr) tys
  unless (isLocalIdent m ocls || any (isLocalIdent m) otcs) $ report $
    warnOrphanInstance p $ pPrint $
    InstanceDecl p WhitespaceLayout cx cls tys []

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
      ms   = classMethods ocls clsEnv
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
warnMissingTypeSignature mid i tys =
  withFixes [prependFix i (render sig ++ "\n") ("Insert type signature '" ++ render sig ++ "'")] $
    spanInfoMessage i $ fsep
      [ text "Top-level binding with no type signature:"
      , nest 2 sig
      ]
  where sig = text (showIdent i) <+> text "::" <+> ppTypeScheme mid tys

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

checkCaseAlts :: SpanInfo -> CaseType -> [Alt ()] -> WCM ()
checkCaseAlts _ _ []      = ok
checkCaseAlts spi ct alts = do
  let spis = map (\(Alt s _ _) -> s) alts
  let pats = map (\(Alt _ pat _) -> [pat]) alts
  let guards = map alt2Guards alts
  (nonExhaustive, overlapped, nondet) <- checkPatternMatching pats guards
  case ct of
    Flex -> do
      unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
        warnMissingPattern spi "an fcase alternative" nonExhaustive
      when (nondet || not (null overlapped)) $ warnFor WarnOverlapping $ report
        $ warnNondetOverlapping spi "An fcase expression"
    Rigid -> do
      unless (null nonExhaustive) $ warnFor WarnIncompletePatterns $ report $
        warnMissingPattern spi "a case alternative" nonExhaustive
      unless (null overlapped) $ mapM_ (\(i, pat) -> warnFor WarnOverlapping $ report $
                                                     warnUnreachablePattern (spis !! i) pat)
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
simplifyPat v@(VariablePattern {}) = return v
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
  simplifyListPattern <$> mapM simplifyPat ps
simplifyPat (AsPattern             _ _ p) = simplifyPat p
simplifyPat (LazyPattern             _ _) = return wildPat
simplifyPat FunctionPattern {}            = return wildPat
simplifyPat InfixFuncPattern {}           = return wildPat

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
        qidAlwaysTrue q = idName (qidIdent q) `elem` ["True", "success", "otherwise"]


-- |Literal patterns are checked by extracting the matched literals
--  and constructing a pattern for any missing case.
processLits :: [EqnInfo] -> WCM ([ExhaustivePats], EqnSet, Bool)
processLits []       = error "WarnCheck.processLits"
processLits qs@(q:_) = do
  -- Check any patterns starting with the literals used
  (missing1, used1, nd1) <- processUsedLits usedLits qs
  if null defaults
    then return (defaultPat : missing1, used1, nd1)
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
  (eps, idxs, nds) <- unzip3 <$> mapM process lits
  return (concat eps, IntSet.unions idxs, or nds)
  where
  process lit = do
    let qs' = [shiftPat q | q <- qs, isVarLit lit (firstPat q)]
        ovlp = length qs' > 1
    (missing, used, nd) <- processEqs qs'
    return ( map (first (LiteralPattern NoSpanInfo () lit :))
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
      then return (map defaultPat unused ++ missing1, used1, nd)
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
  (eps, idxs, nds) <- unzip3 <$> mapM process cons
  return (concat eps, IntSet.unions idxs, or nds)
  where
  process (c, a) = do
    let qs' = [ removeFirstCon c a q | q <- qs , isVarCon c (firstPat q)]
        ovlp = length qs' > 1
    (missing, used, nd) <- processEqs qs'
    return (map (first (makeCon c a)) missing, used, nd && ovlp)

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
  return ( map (first (wildPat :)) missing
         , IntSet.insert n used, nd && ovlp)

-- |Return the constructors of a type not contained in the list of constructors.
getUnusedCons :: [QualIdent] -> WCM [DataConstr]
getUnusedCons []       = internalError "Checks.WarnCheck.getUnusedCons"
getUnusedCons qs@(q:_) = do
  allCons <- getConTy q >>= getTyCons . rootOfType . arrowBase
  return [c | c <- allCons, constrIdent c `notElem` map unqualify qs]

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
        [RenamingType _ _ nc] -> Right [nc]
        _                     -> Left $ "Checks.WarnCheck.getTyCons: " ++ show tc ++ ' ' : show ti ++ '\n' : show tcEnv
      csResult = getTyCons' (qualLookupTypeInfo tc tcEnv)
             <||> getTyCons' (qualLookupTypeInfo tc' tcEnv)
             <||> getTyCons' (lookupTypeInfo (unqualify tc) tcEnv)
            -- Fall back on unqualified lookup if qualified doesn't work
  case csResult of
    Right cs -> return cs
    Left err -> internalError err
  where
    Left _ <||> x = x
    x <||> _ = x

-- |Resugar the exhaustive patterns previously desugared at 'simplifyPat'.
tidyExhaustivePats :: ExhaustivePats -> WCM ExhaustivePats
tidyExhaustivePats (xs, ys) = mapM tidyPat xs >>= \xs' -> return (xs', ys)

-- |Resugar a pattern previously desugared at 'simplifyPat', i.e.
--   * Convert a tuple constructor pattern into a tuple pattern
--   * Convert a list constructor pattern representing a finite list
--     into a list pattern
tidyPat :: Pattern () -> WCM (Pattern ())
tidyPat p@(LiteralPattern {})         = return p
tidyPat p@(VariablePattern {})        = return p
tidyPat p@(ConstructorPattern _ _ c ps)
  | isQTupleId c                      =
    TuplePattern NoSpanInfo <$> mapM tidyPat ps
  | c == qConsId && isFiniteList p    =
    ListPattern NoSpanInfo () <$> mapM tidyPat (unwrapFinite p)
  | c == qConsId                      = unwrapInfinite p
  | otherwise                         =
    ConstructorPattern NoSpanInfo () c <$> mapM tidyPat ps
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
firstPat (_, [],  _) = internalError "Checks.WarnCheck.firstPat: empty list"
firstPat (_, p:_, _) = p

-- |Drop the first pattern of a list.
shiftPat :: EqnInfo -> EqnInfo
shiftPat (_, [],   _ ) = internalError "Checks.WarnCheck.shiftPat: empty list"
shiftPat (n, _:ps, gs) = (n, ps, gs)

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
isLitPat LiteralPattern {} = True
isLitPat _                 = False

-- |Is a pattern a variable pattern?
isVarPat :: Pattern a -> Bool
isVarPat VariablePattern {} = True
isVarPat _                  = False

-- |Is a pattern a constructor pattern?
isConPat :: Pattern a -> Bool
isConPat ConstructorPattern {} = True
isConPat _                     = False

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
  unless (null unused) $ mapM_ (report . warnUnrefVar) unused

reportUnusedTypeVars :: [Ident] -> WCM ()
reportUnusedTypeVars vs = warnFor WarnUnusedBindings $ do
  unused <- filterM isUnrefTypeVar vs
  unless (null unused) $ mapM_ (report . warnUnrefTypeVar) unused

-- ---------------------------------------------------------------------------
-- For detecting unreferenced variables, the following functions update the
-- current check state by adding identifiers occurring in declaration left hand
-- sides.

insertDecl :: Decl a -> WCM ()
insertDecl (DataDecl        _ d _ cs _) = do
  insertTypeConsId d
  mapM_ insertConstrDecl cs
insertDecl (ExternalDataDecl     _ d _) = insertTypeConsId d
insertDecl (NewtypeDecl     _ d _ nc _) = do
  insertTypeConsId d
  insertNewConstrDecl nc
insertDecl (TypeDecl          _ t _ ty) = do
  insertTypeConsId t
  insertTypeExpr ty
insertDecl (FunctionDecl       _ _ f _) = do
  cons <- isConsId f
  unless cons $ insertVar f
insertDecl (ExternalDecl          _ vs) = mapM_ (insertVar . varIdent) vs
insertDecl (PatternDecl          _ p _) = insertPattern False p
insertDecl (FreeDecl              _ vs) = mapM_ (insertVar . varIdent) vs
insertDecl (ClassDecl _ _ _ cls _ _ ds) = do
  insertTypeConsId cls
  mapM_ insertVar $ concatMap methods ds
insertDecl _                            = ok

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
    if fp && var && not (isAnonId v) then visitId v else insertVar v
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
                in  not (all variableVisited (qualLookupNestEnv qid sc))
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
          DataConstructor {}    : _ -> True
          NewtypeConstructor {} : _ -> True
          _                         -> False

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
-- Warn for redundant context
-- ---------------------------------------------------------------------------

-- TODO: Retain and display entire span info for redundant constraints
--       (currently, only the span info for the class name part can be used)

--traverse the AST for QualTypeExpr/Context and check for redundancy
checkRedContext :: [Decl a] -> WCM ()
checkRedContext = warnFor WarnRedundantContext . mapM_ checkRedContextDecl

getRedPredSet :: ModuleIdent -> ClassEnv -> TCEnv -> PredList -> PredList
getRedPredSet m cenv tcEnv pls =
  map (pm Map.!) $ plDifference qps $ minPredList cenv qps --or fromJust $ Map.lookup
  where (qps, pm) = foldr qualifyAndAddPred ([], Map.empty) pls
        qualifyAndAddPred p@(Pred isIcc qid tys) (pls', pm') =
          let qp = Pred isIcc (getOrigName m qid tcEnv) tys
          in (plInsert qp pls', Map.insert qp p pm')

getPredFromContext :: Context -> ([Ident], PredList)
getPredFromContext cx =
  let vs = [v | Constraint _ _ tys <- cx, ty <- tys, v <- typeVariables ty]
  in (vs, toPredList vs OPred cx)

checkRedContext' :: (Pred -> Message) -> PredList -> WCM ()
checkRedContext' f pls = do
  m     <- gets moduleId
  cenv  <- gets classEnv
  tcEnv <- gets tyConsEnv
  mapM_ (report . f) (getRedPredSet m cenv tcEnv pls)

checkRedContextDecl :: Decl a -> WCM ()
checkRedContextDecl (TypeSig _ ids (QualTypeExpr _ cx _)) =
  checkRedContext' (warnRedContext (warnRedFuncString ids) vs) ps
  where (vs, ps) = getPredFromContext cx
checkRedContextDecl (FunctionDecl _ _ _ eqs) = mapM_ checkRedContextEq eqs
checkRedContextDecl (PatternDecl _ _ rhs) = checkRedContextRhs rhs
checkRedContextDecl (ClassDecl _ _ cx i _ _ ds) = do
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
checkRedContextEq (Equation _ _ _ rhs) = checkRedContextRhs rhs

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
-- Warnings messages
-- ---------------------------------------------------------------------------

warnRedFuncString :: [Ident] -> Doc
warnRedFuncString is = text "type signature for function" <>
                       text (if length is == 1 then [] else "s") <+>
                       csep (map (text . escName) is)

-- Doc description -> TypeVars -> Pred -> Warning
warnRedContext :: Doc -> [Ident] -> Pred -> Message
warnRedContext d vs p@(Pred _ qid _) = spanInfoMessage qid $
  text "Redundant context in" <+> d <> colon <+>
  quotes (pPrint $ fromPred vs p) -- idents use ` ' as quotes not ' '

-- seperate a list by ', '
csep :: [Doc] -> Doc
csep []     = empty
csep [x]    = x
csep (x:xs) = x <> comma <+> csep xs

warnUnrefTypeVar :: Ident -> Message
warnUnrefTypeVar = warnUnref "Unreferenced type variable"

warnUnrefVar :: Ident -> Message
warnUnrefVar = warnUnref "Unused declaration of variable"

warnUnref :: String -> Ident -> Message
warnUnref msg v =
  withFixes [replaceFix v "_" ("Replace " ++ escName v ++ " with _")] $
    spanInfoMessage v $ hsep $ map text
      [ msg, escName v ]

warnShadowing :: Ident -> Ident -> Message
warnShadowing x v = spanInfoMessage x $
  text "Shadowing symbol" <+> text (escName x)
  <> comma <+> text "bound at:" <+> ppPosition (getPosition v)
