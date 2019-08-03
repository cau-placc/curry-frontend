{-|
Module      : Checks.SyntaxCheck
Description : Checks the syntax of a Curry module
Copyright   : (c) 1999–2004 Wolfgang Lux, Martin Engelke, Björn Peemöller
                  2015 Jan Tikovsky
                  2016 Finn Teegen
                  2019 Jan-Hendrik Matthes
License     : BSD-3-Clause

Maintainer  : fte@informatik.uni-kiel.de
Stability   : experimental
Portability : portable

After the type declarations have been checked, the compiler performs a syntax
check on the remaining declarations. This check disambiguates nullary data
constructors and variables which -- in contrast to Haskell -- is not possible
on purely syntactic criteria. In addition, this pass checks for undefined as
well as ambiguous variables and constructors. In order to allow lifting of
local definitions in later phases, all local variables are renamed by adding a
key identifying their scope. Therefore, all variables defined in the same scope
share the same key so that multiple definitions can be recognized. Finally, all
(adjacent) equations of a function are merged into a single definition.
-}

{-# LANGUAGE CPP #-}

module Checks.SyntaxCheck (syntaxCheck) where

#if __GLASGOW_HASKELL__ >= 804
import           Prelude             hiding ((<>))
#endif

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative ((<$>), (<*>))
#endif

import           Control.Monad       (unless, when)
import           Control.Monad.Extra (allM, unlessM)
import qualified Control.Monad.State as S (State, gets, modify, runState,
                                           withState)
import           Data.Function       (on)
import           Data.List           (insertBy, intersect, nub, nubBy)
import qualified Data.Map            as Map (Map, empty, findWithDefault,
                                             fromList, insertWith, keys)
import           Data.Maybe          (isJust, isNothing)
import qualified Data.Set            as Set (Set, empty, insert, member,
                                             singleton, toList, union)

import           Curry.Base.Ident
import           Curry.Base.Position
import           Curry.Base.Pretty
import           Curry.Base.Span
import           Curry.Base.SpanInfo
import           Curry.Syntax
import           Curry.Syntax.Pretty (ppPattern, ppTypeExpr)

import           Base.CurryTypes
import           Base.Expr
import           Base.Messages       (Message, internalError, posMessage)
import           Base.NestEnv
import           Base.SCC            (scc)
import           Base.Utils          (findDouble, findMultiples, (++!))

import           Env.TypeConstructor (TCEnv, TypeInfo (..), clsMethods,
                                      qualLookupTypeInfo)
import           Env.Value           (ValueEnv, ValueInfo (..))

-- The syntax checking proceeds as follows. First, the compiler extracts
-- information about all imported values and data constructors from the
-- imported (type) environments. Next, the data constructors defined in
-- the current module are entered into this environment. After this,
-- all record labels are entered into the environment. If a record
-- identifier is already assigned to a constructor, then an error will be
-- generated. Class methods defined in the current module are entered into
-- the environment, too. Finally, all declarations are checked within the
-- resulting environment. In addition, this process will also rename the
-- local variables.

-- TODO: use SpanInfos for errors and then stop passing down SpanInfo from the decls to the checks

syntaxCheck :: [KnownExtension] -> TCEnv -> ValueEnv -> Module ()
            -> ((Module (), [KnownExtension]), [Message])
syntaxCheck exts tcEnv vEnv mdl@(Module _ _ m _ _ ds) =
  case findMultiples cons of
    []  -> case findMultiples (ls ++ fs ++ cons ++ cs) of
             []  -> runSC (checkModule mdl) state
             iss -> ((mdl, exts), map (errMultipleDeclarations m) iss)
    css -> ((mdl, exts), map errMultipleDataConstructor css)
  where
    tds   = filter isTypeDecl ds
    vds   = filter isValueDecl ds
    cds   = filter isClassDecl ds
    cons  = concatMap constrs tds
    ls    = nub $ concatMap recLabels tds
    fs    = nub $ concatMap vars vds
    cs    = concatMap (concatMap methods) [ds' | ClassDecl _ _ _ _ ds' <- cds]
    rEnv  = globalEnv $ fmap renameInfo vEnv
    state = initState exts m tcEnv rEnv

-- A global state transformer is used for generating fresh integer keys with
-- which the variables are renamed.
-- The state tracks the identifier of the current scope 'scopeId' as well as
-- the next fresh identifier, which is used for introducing new scopes as well
-- as renaming literals and underscore to disambiguate them.

-- |Syntax check monad
type SCM = S.State SCState

-- |Internal state of the syntax check
data SCState = SCState
  { extensions       :: [KnownExtension] -- ^ Enabled language extensions
  , moduleIdent      :: ModuleIdent      -- ^ 'ModuleIdent' of the current module
  , tyConsEnv        :: TCEnv
  , renameEnv        :: RenameEnv        -- ^ Information store
  , scopeId          :: Integer          -- ^ Identifier for the current scope
  , nextId           :: Integer          -- ^ Next fresh identifier
  , funcDeps         :: FuncDeps         -- ^ Stores data about functions dependencies
  , typeClassesCheck :: Bool
  , errors           :: [Message]        -- ^ Syntactic errors in the module
  }

-- |Initial syntax check state
initState :: [KnownExtension] -> ModuleIdent -> TCEnv -> RenameEnv -> SCState
initState exts m tcEnv rEnv =
  SCState exts m tcEnv rEnv globalScopeId 1 noFuncDeps False []

-- |Identifier for global (top-level) declarations
globalScopeId :: Integer
globalScopeId = idUnique (mkIdent "")

-- |Run the syntax check monad
runSC :: SCM a -> SCState -> (a, [Message])
runSC scm s = let (a, s') = S.runState scm s in (a, reverse $ errors s')

-- |Check for an enabled extension
hasExtension :: KnownExtension -> SCM Bool
hasExtension ext = S.gets (elem ext . extensions)

-- |Enable an additional 'Extension' to avoid redundant complaints about
-- missing extensions
enableExtension :: KnownExtension -> SCM ()
enableExtension e = S.modify $ \s -> s { extensions = e : extensions s }

-- |Retrieve all enabled extensions
getExtensions :: SCM [KnownExtension]
getExtensions = S.gets extensions

-- |Retrieve the 'ModuleIdent' of the current module
getModuleIdent :: SCM ModuleIdent
getModuleIdent = S.gets moduleIdent

-- |Retrieve the 'TCEnv'
getTyConsEnv :: SCM TCEnv
getTyConsEnv = S.gets tyConsEnv

-- |Retrieve the 'RenameEnv'
getRenameEnv :: SCM RenameEnv
getRenameEnv = S.gets renameEnv

-- |Modify the 'RenameEnv'
modifyRenameEnv :: (RenameEnv -> RenameEnv) -> SCM ()
modifyRenameEnv f = S.modify $ \s -> s { renameEnv = f $ renameEnv s }

-- |Retrieve the current scope identifier
getScopeId :: SCM Integer
getScopeId = S.gets scopeId

-- |Create a new identifier and return it
newId :: SCM Integer
newId = do
  curId <- S.gets nextId
  S.modify $ \s -> s { nextId = succ curId }
  return curId

-- |Checks whether a type classes check is running
isTypeClassesCheck :: SCM Bool
isTypeClassesCheck = S.gets typeClassesCheck

-- |Performs a type classes check in a nested scope
performTypeClassesCheck :: SCM a -> SCM a
performTypeClassesCheck = inNestedScope .
  S.withState (\s -> s { typeClassesCheck = True })

-- |Increase the nesting of the 'RenameEnv' to introduce a new local scope.
-- This also increases the scope identifier.
incNesting :: SCM ()
incNesting = do
  newScopeId <- newId
  S.modify $ \s -> s { scopeId = newScopeId }
  modifyRenameEnv nestEnv

withLocalEnv :: SCM a -> SCM a
withLocalEnv act = do
  oldEnv <- getRenameEnv
  res    <- act
  modifyRenameEnv $ const oldEnv
  return res

-- |Perform an action in a nested scope (by creating a nested 'RenameEnv')
-- and discard the nested 'RenameEnv' afterwards
inNestedScope :: SCM a -> SCM a
inNestedScope act = withLocalEnv (incNesting >> act)

-- |Modify the `FuncDeps'
modifyFuncDeps :: (FuncDeps -> FuncDeps) -> SCM ()
modifyFuncDeps f = S.modify $ \ s -> s { funcDeps = f $ funcDeps s }

-- |Report a syntax error
report :: Message -> SCM ()
report msg = S.modify $ \s -> s { errors = msg : errors s }

-- |Everything is checked
ok :: SCM ()
ok = return ()

-- FuncDeps contains information to deal with dependencies between functions.
-- This is used for checking whether functional patterns are cyclic.
-- curGlobalFunc contains the identifier of the global function that is
-- currently being checked, if any.
-- data X = X
-- f = let g = lookup 42 in g [1,2,3]
-- While `X' is being checked `curGlobalFunc' should be `Nothing',
-- while `lookup' is being checked is should be `f's identifier.
-- globalDeps collects all dependencies (other functions) of global functions
-- funcPats collects all functional patterns and the global function they're
-- used in
data FuncDeps = FuncDeps
  { curGlobalFunc :: Maybe QualIdent
  , globalDeps    :: GlobalDeps
  , funcPats      :: [(QualIdent, QualIdent)]
  }
type GlobalDeps = Map.Map QualIdent (Set.Set QualIdent)

-- |Initial state for FuncDeps
noFuncDeps :: FuncDeps
noFuncDeps = FuncDeps Nothing Map.empty []

-- |Perform an action inside a function, settìng `curGlobalFunc' to that function
inFunc :: Ident -> SCM a -> SCM a
inFunc i scm = do
  m      <- getModuleIdent
  global <- isNothing <$> S.gets (curGlobalFunc . funcDeps)
  when global $ modifyFuncDeps $ \ fd -> fd { curGlobalFunc = Just (qualifyWith m i) }
  res    <- scm
  when global $ modifyFuncDeps $ \ fd -> fd { curGlobalFunc = Nothing }
  return res

-- |Add a dependency to `curGlobalFunction'
addGlobalDep :: QualIdent -> SCM ()
addGlobalDep dep = do
  maybeF <- S.gets (curGlobalFunc . funcDeps)
  case maybeF of
    Nothing -> internalError "SyntaxCheck.addFuncPat: no global function set"
    Just  f -> modifyFuncDeps $ \ fd -> fd
                { globalDeps = Map.insertWith Set.union f
                              (Set.singleton dep) (globalDeps fd) }

-- |Add a functional pattern to `curGlobalFunction'
addFuncPat :: QualIdent -> SCM ()
addFuncPat fp = do
  maybeF <- S.gets (curGlobalFunc . funcDeps)
  case maybeF of
    Nothing -> internalError "SyntaxCheck.addFuncPat: no global function set"
    Just  f -> modifyFuncDeps $ \ fd -> fd { funcPats = (fp, f) : funcPats fd }

-- |Return dependencies of global functions
getGlobalDeps :: SCM GlobalDeps
getGlobalDeps = globalDeps <$> S.gets funcDeps

-- |Return used functional patterns
getFuncPats :: SCM [(QualIdent, QualIdent)]
getFuncPats = funcPats <$> S.gets funcDeps


-- A nested environment is used for recording information about the data
-- constructors and variables in the module. For every data constructor
-- its arity is saved. This is used for checking that all constructor
-- applications in patterns are saturated. For local variables the
-- environment records the new name of the variable after renaming.
-- Global variables are recorded with qualified identifiers in order
-- to distinguish multiply declared entities.

-- Currently, records must explicitly be declared together with their labels.
-- When constructing or updating a record, it is necessary to compute
-- all its labels using just one of them. Thus for each label
-- the record identifier and all its labels are entered into the environment

-- Note: the function 'qualLookupVar' has been extended to allow the usage of
-- the qualified list constructor (prelude.:).

type RenameEnv = NestEnv RenameInfo

data RenameInfo
  -- |Arity of data constructor
  = Constr      QualIdent Int
  -- |Constructors of a record label
  | RecordLabel QualIdent [QualIdent]
  -- |Arity of global function
  | GlobalVar   QualIdent Int
  -- |Arity of local function
  | LocalVar    Ident Int
    deriving (Eq, Show)

ppRenameInfo :: RenameInfo -> Doc
ppRenameInfo (Constr      qn _) = text (escQualName qn)
ppRenameInfo (RecordLabel qn _) = text (escQualName qn)
ppRenameInfo (GlobalVar   qn _) = text (escQualName qn)
ppRenameInfo (LocalVar     n _) = text (escName      n)

-- Since record types are currently translated into data types, it is necessary
-- to ensure that all identifiers for records and constructors are different.
-- Furthermore, it is not allowed to declare a label more than once.

renameInfo :: ValueInfo -> RenameInfo
renameInfo (DataConstructor    qid    a _ _) = Constr      qid a
renameInfo (NewtypeConstructor qid      _ _) = Constr      qid 1
renameInfo (Value              qid _  a   _) = GlobalVar   qid a
renameInfo (Label              qid cs     _) = RecordLabel qid cs

bindGlobal :: Bool -> ModuleIdent -> Ident -> RenameInfo -> RenameEnv
           -> RenameEnv
bindGlobal tcc m c r
  | not tcc   = bindNestEnv c r . qualBindNestEnv (qualifyWith m c) r
  | otherwise = id

bindLocal :: Ident -> RenameInfo -> RenameEnv -> RenameEnv
bindLocal = bindNestEnv

-- ------------------------------------------------------------------------------

-- |Bind type constructor information and record label information
bindTypeDecl :: Decl a -> SCM ()
bindTypeDecl (DataDecl    _ _ _ cs _) =
  mapM_ bindConstr cs >> bindRecordLabels cs
bindTypeDecl (NewtypeDecl _ _ _ nc _) = bindNewConstr nc
bindTypeDecl _                        = ok

bindConstr :: ConstrDecl -> SCM ()
bindConstr (ConstrDecl _ c tys) = do
  m <- getModuleIdent
  modifyRenameEnv $ bindGlobal False m c (Constr (qualifyWith m c) $ length tys)
bindConstr (ConOpDecl _ _ op _) = do
  m <- getModuleIdent
  modifyRenameEnv $ bindGlobal False m op (Constr (qualifyWith m op) 2)
bindConstr (RecordDecl _ c fs)  = do
  m <- getModuleIdent
  modifyRenameEnv $ bindGlobal False m c (Constr (qualifyWith m c) (length labels))
    where labels = [l | FieldDecl _ ls _ <- fs, l <- ls]

bindNewConstr :: NewConstrDecl -> SCM ()
bindNewConstr (NewConstrDecl _ c _) = do
  m <- getModuleIdent
  modifyRenameEnv $ bindGlobal False m c (Constr (qualifyWith m c) 1)
bindNewConstr (NewRecordDecl _ c (l, _)) = do
  m <- getModuleIdent
  bindRecordLabel (l, [c])
  modifyRenameEnv $ bindGlobal False m c (Constr (qualifyWith m c) 1)

bindRecordLabels :: [ConstrDecl] -> SCM ()
bindRecordLabels cs =
  mapM_ bindRecordLabel [(l, constr l) | l <- nub (concatMap recordLabels cs)]
  where constr l = [constrId c | c <- cs, l `elem` recordLabels c]

bindRecordLabel :: (Ident, [Ident]) -> SCM ()
bindRecordLabel (l, cs) = do
  m   <- getModuleIdent
  new <- (null . lookupVar l) <$> getRenameEnv
  unless new $ report $ errDuplicateDefinition l
  modifyRenameEnv $ bindGlobal False m l $
    RecordLabel (qualifyWith m l) (map (qualifyWith m) cs)

-- ------------------------------------------------------------------------------

-- |Bind a global function declaration in the 'RenameEnv'
bindFuncDecl :: Bool -> ModuleIdent -> Decl a -> RenameEnv -> RenameEnv
bindFuncDecl _   _ (FunctionDecl _ _ _ []) _
  = internalError "SyntaxCheck.bindFuncDecl: no equations"
bindFuncDecl tcc m (FunctionDecl _ _ f (eq:_)) env
  = let arty = length $ snd $ getFlatLhs eq
    in  bindGlobal tcc m f (GlobalVar (qualifyWith m f) arty) env
bindFuncDecl tcc m (TypeSig spi fs (ContextType _ _ ty)) env
  = bindFuncDecl tcc m (TypeSig spi fs ty) env
bindFuncDecl tcc m (TypeSig _ fs ty) env
  = foldr bindTS env $ map (qualifyWith m) fs
  where
    bindTS qf env'
      | null $ qualLookupVar qf env'
        = bindGlobal tcc m (unqualify qf) (GlobalVar qf (typeArity ty)) env'
      | otherwise = env'
bindFuncDecl _   _ _ env = env

-- ------------------------------------------------------------------------------

-- |Bind type class information, i.e. class methods
bindClassDecl :: Decl a -> SCM ()
bindClassDecl (ClassDecl _ _ _ _ ds) = mapM_ bindClassMethod ds
bindClassDecl _                      = ok

bindClassMethod :: Decl a -> SCM ()
bindClassMethod ts@(TypeSig _ _ _) = do
  m <- getModuleIdent
  modifyRenameEnv $ bindFuncDecl False m ts
bindClassMethod _ = ok

-- ------------------------------------------------------------------------------

-- |Bind a local declaration (function, variables) in the 'RenameEnv'
bindVarDecl :: Decl a -> RenameEnv -> RenameEnv
bindVarDecl (FunctionDecl    _ _ f eqs) env
  | null eqs  = internalError "SyntaxCheck.bindVarDecl: no equations"
  | otherwise = let arty = length $ snd $ getFlatLhs $ head eqs
                in  bindLocal (unRenameIdent f) (LocalVar f arty) env
bindVarDecl (PatternDecl         _ t _) env = foldr bindVar env (bv t)
bindVarDecl (FreeDecl             _ vs) env =
  foldr bindVar env (map varIdent vs)
bindVarDecl _                           env = env

bindVar :: Ident -> RenameEnv -> RenameEnv
bindVar v | isAnonId v = id
          | otherwise  = bindLocal (unRenameIdent v) (LocalVar v 0)

lookupVar :: Ident -> RenameEnv -> [RenameInfo]
lookupVar v env = lookupNestEnv v env ++! lookupTupleConstr v

qualLookupVar :: QualIdent -> RenameEnv -> [RenameInfo]
qualLookupVar v env =  qualLookupNestEnv v env
                   ++! qualLookupListCons v env
                   ++! lookupTupleConstr (unqualify v)

lookupTupleConstr :: Ident -> [RenameInfo]
lookupTupleConstr v
  | isTupleId v = let a = tupleArity v
                  in  [Constr (qualifyWith preludeMIdent $ tupleId a) a]
  | otherwise   = []

qualLookupListCons :: QualIdent -> RenameEnv -> [RenameInfo]
qualLookupListCons v env
  | v == qualifyWith preludeMIdent consId
  = qualLookupNestEnv (qualify $ qidIdent v) env
  | otherwise
  = []

-- When a module is checked, the global declaration group is checked. The
-- resulting renaming environment can be discarded. The same is true for
-- a goal. Note that all declarations in the goal must be considered as
-- local declarations. Class and instance declarations define their own scope,
-- thus defined functions will be renamed as well. For class and instance
-- declarations several checks have to be disabled (for instance, type
-- signatures without corresponding function declaration are allowed in class
-- declarations), while some have to be performed extra (for instance, no
-- other functions than specified by the type signatures within a class
-- declaration are allowed to be declared).

checkModule :: Module () -> SCM (Module (), [KnownExtension])
checkModule (Module spi ps m es is ds) = do
  mapM_ checkImpredDecl ds
  mapM_ bindTypeDecl tds
  mapM_ bindClassDecl cds
  ds' <- checkTopDecls ds
  cds' <- mapM (performTypeClassesCheck . checkClassDecl) cds
  ids' <- mapM (performTypeClassesCheck . checkInstanceDecl) ids
  let ds'' = updateClassAndInstanceDecls cds' ids' ds'
  checkFuncPatDeps
  exts <- getExtensions
  return (Module spi ps m es is ds'', exts)
  where tds = filter isTypeDecl ds
        cds = filter isClassDecl ds
        ids = filter isInstanceDecl ds

-- |Checks whether a function in a functional pattern contains cycles
-- |(depends on its own global function)
checkFuncPatDeps :: SCM ()
checkFuncPatDeps = do
  fps  <- getFuncPats
  deps <- getGlobalDeps
  let levels   = scc (:[])
                     (\k -> Set.toList (Map.findWithDefault (Set.empty) k deps))
                     (Map.keys deps)
      levelMap = Map.fromList [ (f, l) | (fs, l) <- zip levels [1 ..], f <- fs ]
      level f  = Map.findWithDefault (0 :: Int) f levelMap
  mapM_ (checkFuncPatDep level) fps

checkFuncPatDep :: Ord a => (QualIdent -> a) -> (QualIdent, QualIdent) -> SCM ()
checkFuncPatDep level (fp, f) = unless (level fp < level f) $
  report $ errFuncPatCyclic fp f

checkTopDecls :: [Decl ()] -> SCM [Decl ()]
checkTopDecls ds = do
  m <- getModuleIdent
  tcc <- isTypeClassesCheck
  checkDeclGroup (bindFuncDecl tcc m) ds

checkClassDecl :: Decl () -> SCM (Decl ())
checkClassDecl (ClassDecl p cx cls tv ds) = do
  checkMethods (qualify cls) (concatMap methods ds) ds
  ClassDecl p cx cls tv <$> checkTopDecls ds
checkClassDecl _ =
  internalError "SyntaxCheck.checkClassDecl: no class declaration"

checkInstanceDecl :: Decl () -> SCM (Decl ())
checkInstanceDecl (InstanceDecl p cx qcls ty ds) = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  checkMethods qcls (clsMethods m qcls tcEnv) ds
  InstanceDecl p cx qcls ty <$> checkTopDecls ds
checkInstanceDecl _ =
  internalError "SyntaxCheck.checkInstanceDecl: no instance declaration"

checkMethods :: QualIdent -> [Ident] -> [Decl a] -> SCM ()
checkMethods qcls ms ds =
  mapM_ (report . errUndefinedMethod qcls) $ filter (`notElem` ms) fs
  where fs = [f | FunctionDecl _ _ f _ <- ds]

updateClassAndInstanceDecls :: [Decl a] -> [Decl a] -> [Decl a] -> [Decl a]
updateClassAndInstanceDecls [] [] ds = ds
updateClassAndInstanceDecls (c:cs) is (ClassDecl _ _ _ _ _:ds) =
  c : updateClassAndInstanceDecls cs is ds
updateClassAndInstanceDecls cs (i:is) (InstanceDecl _ _ _ _ _:ds) =
  i : updateClassAndInstanceDecls cs is ds
updateClassAndInstanceDecls cs is (d:ds) =
  d : updateClassAndInstanceDecls cs is ds
updateClassAndInstanceDecls _ _ _ =
  internalError "SyntaxCheck.updateClassAndInstanceDecls"

-- Each declaration group opens a new scope and uses a distinct key
-- for renaming the variables in this scope. In a declaration group,
-- first the left hand sides of all declarations are checked, next the
-- compiler checks that there is a definition for every type signature
-- and evaluation annotation in this group. Finally, the right hand sides
-- are checked and adjacent equations for the same function are merged
-- into a single definition.

-- The function 'checkDeclLhs' also handles the case where a pattern
-- declaration is recognized as a function declaration by the parser.
-- This happens, e.g., for the declaration
--      where Just x = y
-- because the parser cannot distinguish nullary constructors and functions.
-- Note that pattern declarations are not allowed on the top-level.

checkDeclGroup :: (Decl () -> RenameEnv -> RenameEnv) -> [Decl ()] -> SCM [Decl ()]
checkDeclGroup bindDecl ds = do
  checkedLhs <- mapM checkDeclLhs $ sortFuncDecls ds
  joinEquations checkedLhs >>= checkDecls bindDecl

checkDeclLhs :: Decl () -> SCM (Decl ())
checkDeclLhs (InfixDecl    p fix' pr ops) =
  InfixDecl p fix' <$> checkPrecedence p pr <*> mapM renameVar ops
checkDeclLhs (TypeSig            p vs ty) =
  (\vs' -> TypeSig p vs' ty) <$> mapM (checkVar "type signature") vs
checkDeclLhs (FunctionDecl     p _ f eqs) =
  inFunc f $ checkEquationsLhs p eqs
checkDeclLhs (ExternalDecl          p vs) =
  ExternalDecl p <$> mapM (checkVar' "external declaration") vs
checkDeclLhs (PatternDecl        p t rhs) =
  (\t' -> PatternDecl p t' rhs) <$> checkPattern p t
checkDeclLhs (FreeDecl              p vs) =
  FreeDecl p <$> mapM (checkVar' "free variables declaration") vs
checkDeclLhs d                            = return d

checkPrecedence :: SpanInfo -> Maybe Precedence -> SCM (Maybe Precedence)
checkPrecedence _ Nothing  = return Nothing
checkPrecedence p (Just i) = do
  unless (0 <= i && i <= 9) $ report
                            $ errPrecedenceOutOfRange (spanInfo2Pos p) i
  return $ Just i

checkVar' :: String -> Var a -> SCM (Var a)
checkVar' what (Var a v) = Var a <$> checkVar what v

checkVar :: String -> Ident -> SCM Ident
checkVar _what v = do
  -- isDC <- S.gets (isDataConstr v . renameEnv)
  -- when isDC $ report $ nonVariable what v -- TODO Why is this disabled?
  renameVar v

renameVar :: Ident -> SCM Ident
renameVar v = renameIdent v <$> getScopeId

checkEquationsLhs :: SpanInfo -> [Equation ()] -> SCM (Decl ())
checkEquationsLhs p [Equation p' lhs rhs] = do
  lhs' <- checkEqLhs p' lhs
  case lhs' of
    Left  l -> return $ funDecl' l
    Right r -> checkDeclLhs (PatternDecl p' r rhs)
  where funDecl' (f, lhs') = FunctionDecl p () f [Equation p' lhs' rhs]
checkEquationsLhs _ _ = internalError "SyntaxCheck.checkEquationsLhs"

checkEqLhs :: SpanInfo -> Lhs () -> SCM (Either (Ident, Lhs ()) (Pattern ()))
checkEqLhs pspi toplhs = do
  m   <- getModuleIdent
  k   <- getScopeId
  env <- getRenameEnv
  case toplhs of
    FunLhs spi f ts
      | not $ isDataConstr f env -> return left
      | k /= globalScopeId       -> return right
      | null infos               -> return left
      | otherwise                -> do report $ errToplevelPattern p
                                       return right
      where f'    = renameIdent f k
            infos = qualLookupVar (qualifyWith m f) env
            left  = Left  (f', FunLhs spi f' ts)
            right = Right $  -- use start from the parsed FunLhs and compute end
              updateEndPos $ ConstructorPattern spi () (qualify f) ts
    OpLhs spi t1 op t2
      | not $ isDataConstr op env -> return left
      | k /= globalScopeId        -> return right
      | null infos                -> return left
      | otherwise                 -> do report $ errToplevelPattern p
                                        return right
      where op'   = renameIdent op k
            infos = qualLookupVar (qualifyWith m op) env
            left  = Left (op', OpLhs spi t1 op' t2)
            right = checkOpLhs k env (infixPattern t1 (qualify op)) t2
            infixPattern (InfixPattern _ a' t1' op1 t2') op2 t3 =
              let t2'' = infixPattern t2' op2 t3
                  sp = combineSpans (getSrcSpan t1') (getSrcSpan t2'')
              in InfixPattern (fromSrcSpan sp) a' t1' op1 t2''
            infixPattern t1' op1 t2' =
              let sp = combineSpans (getSrcSpan t1') (getSrcSpan t2')
              in InfixPattern (fromSrcSpan sp) () t1' op1 t2'
    ApLhs spi lhs ts -> do
      checked <- checkEqLhs pspi lhs
      case checked of
        Left (f', lhs') -> return $ Left (f', updateEndPos $ ApLhs spi lhs' ts)
        r               -> do report $ errNonVariable "curried definition" f
                              return $ r
        where (f, _) = flatLhs lhs
  where p = spanInfo2Pos pspi

checkOpLhs :: Integer -> RenameEnv -> (Pattern a -> Pattern a)
           -> Pattern a -> Either (Ident, Lhs a) (Pattern a)
checkOpLhs k env f (InfixPattern spi a t1 op t2)
  | isJust m || isDataConstr op' env
  = checkOpLhs k env (f . InfixPattern spi a t1 op) t2
  | otherwise
  = Left (op'', OpLhs (getSpanInfo t1') t1' op'' t2)
  where (m,op') = (qidModule op, qidIdent op)
        op''    = renameIdent op' k
        t1'     = f t1
checkOpLhs _ _ f t = Right (f t)

-- -- ---------------------------------------------------------------------------

joinEquations :: [Decl a] -> SCM [Decl a]
joinEquations [] = return []
joinEquations (FunctionDecl a p f eqs : FunctionDecl _ _ f' [eq] : ds)
  | f == f' = do
    when (getArity (head eqs) /= getArity eq) $ report $ errDifferentArity [f, f']
    joinEquations (updateEndPos (FunctionDecl a p f (eqs ++ [eq])) : ds)
  where getArity = length . snd . getFlatLhs
joinEquations (d : ds) = (d :) <$> joinEquations ds

checkDecls :: (Decl () -> RenameEnv -> RenameEnv) -> [Decl ()] -> SCM [Decl ()]
checkDecls bindDecl ds = do
  let dblVar = findDouble bvs
  onJust (report . errDuplicateDefinition) dblVar
  let mulTys = findMultiples tys
  mapM_ (report . errDuplicateTypeSig) mulTys
  let missingTys = [v | ExternalDecl _ vs <- ds, Var _ v <- vs, v `notElem` tys]
  mapM_ (report . errNoTypeSig) missingTys
  if isNothing dblVar && null mulTys && null missingTys
    then do
      modifyRenameEnv $ \env -> foldr bindDecl env (tds ++ vds)
      mapM (checkDeclRhs bvs) ds
    else return ds -- skip further checking
  where vds    = filter isValueDecl ds
        tds    = filter isTypeSig ds
        bvs    = concatMap vars vds
        tys    = concatMap vars tds
        onJust = maybe ok

-- -- ---------------------------------------------------------------------------

checkDeclRhs :: [Ident] -> Decl () -> SCM (Decl ())
checkDeclRhs _   (DataDecl   p tc tvs cs clss) =
  flip (DataDecl p tc tvs) clss <$> mapM checkDeclLabels cs
checkDeclRhs bvs (TypeSig        p vs ty) =
  (\vs' -> TypeSig p vs' ty) <$> mapM (checkLocalVar bvs) vs
checkDeclRhs _   (FunctionDecl a p f eqs) =
  FunctionDecl a p f <$> inFunc f (mapM checkEquation eqs)
checkDeclRhs _   (PatternDecl    p t rhs) =
  PatternDecl p t <$> checkRhs rhs
checkDeclRhs _   d                        = return d

checkDeclLabels :: ConstrDecl -> SCM ConstrDecl
checkDeclLabels rd@(RecordDecl _ _ fs) = do
  onJust (report . errDuplicateLabel "declaration")
         (findDouble $ map qualify labels)
  return rd
  where
    onJust = maybe ok
    labels = [l | FieldDecl _ ls _ <- fs, l <- ls]
checkDeclLabels d = return d

checkLocalVar :: [Ident] -> Ident -> SCM Ident
checkLocalVar bvs v = do
  tcc <- isTypeClassesCheck
  when (v `notElem` bvs && not tcc) $ report $ errNoBody v
  return v

checkEquation :: Equation () -> SCM (Equation ())
checkEquation (Equation p lhs rhs) = inNestedScope $ do
  lhs' <- checkLhs p lhs >>= addBoundVariables False
  rhs' <- checkRhs rhs
  return $ Equation p lhs' rhs'

checkLhs :: SpanInfo -> Lhs () -> SCM (Lhs ())
checkLhs p (FunLhs    spi f ts) = FunLhs spi f <$> mapM (checkPattern p) ts
checkLhs p (OpLhs spi t1 op t2) = do
  let wrongCalls = concatMap (checkParenPattern (Just $ qualify op)) [t1,t2]
  unless (null wrongCalls) $ report $ errInfixWithoutParens
    (getPosition op) wrongCalls
  flip (OpLhs spi) op <$> checkPattern p t1 <*> checkPattern p t2
checkLhs p (ApLhs   spi lhs ts) =
  ApLhs spi <$> checkLhs p lhs <*> mapM (checkPattern p) ts

-- checkParen
-- @param Aufrufende InfixFunktion
-- @param Pattern
-- @return Liste mit fehlerhaften Funktionsaufrufen

checkParenPattern :: Maybe QualIdent -> Pattern a -> [(QualIdent, QualIdent)]
checkParenPattern _ (LiteralPattern          _ _ _) = []
checkParenPattern _ (NegativePattern         _ _ _) = []
checkParenPattern _ (VariablePattern         _ _ _) = []
checkParenPattern _ (ConstructorPattern   _ _ _ cs) =
  concatMap (checkParenPattern Nothing) cs
checkParenPattern o (InfixPattern     _ _ t1 op t2) =
  maybe [] (\c -> [(c, op)]) o
  ++ checkParenPattern Nothing t1 ++ checkParenPattern Nothing t2
checkParenPattern _ (ParenPattern              _ t) =
  checkParenPattern Nothing t
checkParenPattern _ (RecordPattern        _ _ _ fs) =
  concatMap (\(Field _ _ t) -> checkParenPattern Nothing t) fs
checkParenPattern _ (TuplePattern             _ ts) =
  concatMap (checkParenPattern Nothing) ts
checkParenPattern _ (ListPattern            _ _ ts) =
  concatMap (checkParenPattern Nothing) ts
checkParenPattern o (AsPattern               _ _ t) =
  checkParenPattern o t
checkParenPattern o (LazyPattern               _ t) =
  checkParenPattern o t
checkParenPattern _ (FunctionPattern      _ _ _ ts) =
  concatMap (checkParenPattern Nothing) ts
checkParenPattern o (InfixFuncPattern _ _ t1 op t2) =
  maybe [] (\c -> [(c, op)]) o
  ++ checkParenPattern Nothing t1 ++ checkParenPattern Nothing t2

checkPattern :: SpanInfo -> Pattern () -> SCM (Pattern ())
checkPattern _ (LiteralPattern        spi a l) =
  return $ LiteralPattern spi a l
checkPattern _ (NegativePattern       spi a l) =
  return $ NegativePattern spi a l
checkPattern p (VariablePattern       spi a v)
  | isAnonId v = (VariablePattern spi a . renameIdent v) <$> newId
  | otherwise  = checkConstructorPattern p spi (qualify v) []
checkPattern p (ConstructorPattern spi _ c ts) =
  checkConstructorPattern p spi c ts
checkPattern p (InfixPattern   spi _ t1 op t2) =
  checkInfixPattern p spi t1 op t2
checkPattern p (ParenPattern            spi t) =
  ParenPattern spi <$> checkPattern p t
checkPattern p (RecordPattern      spi _ c fs) =
  checkRecordPattern p spi c fs
checkPattern p (TuplePattern           spi ts) =
  TuplePattern spi <$> mapM (checkPattern p) ts
checkPattern p (ListPattern          spi a ts) =
  ListPattern spi a <$> mapM (checkPattern p) ts
checkPattern p (AsPattern             spi v t) =
  AsPattern spi <$> checkVar "@ pattern" v <*> checkPattern p t
checkPattern p (LazyPattern             spi t) = do
  t' <- checkPattern p t
  banFPTerm "lazy pattern" p t'
  return (LazyPattern spi t')
checkPattern _ (FunctionPattern     _ _ _ _) = internalError $
  "SyntaxCheck.checkPattern: function pattern not defined"
checkPattern _ (InfixFuncPattern  _ _ _ _ _) = internalError $
  "SyntaxCheck.checkPattern: infix function pattern not defined"

checkConstructorPattern :: SpanInfo -> SpanInfo -> QualIdent -> [Pattern ()]
                        -> SCM (Pattern ())
checkConstructorPattern p spi c ts = do
  env <- getRenameEnv
  m <- getModuleIdent
  k <- getScopeId
  case qualLookupVar c env of
    [Constr _ n] -> processCons c n
    [r]          -> processVarFun r k
    rs -> case qualLookupVar (qualQualify m c) env of
      [Constr _ n] -> processCons (qualQualify m c) n
      [r]          -> processVarFun r k
      []
        | null ts && not (isQualified c) ->
            return $ VariablePattern spi () $ renameIdent (unqualify c) k
        | null rs -> do
            ts' <- mapM (checkPattern p) ts
            report $ errUndefinedData c
            return $ ConstructorPattern spi () c ts'
      _ -> do ts' <- mapM (checkPattern p) ts
              report $ errAmbiguousData rs c
              return $ ConstructorPattern spi () c ts'
  where
  n' = length ts
  processCons qc n = do
    when (n /= n') $ report $ errWrongArity c n n'
    ConstructorPattern spi () qc <$> mapM (checkPattern p) ts
  processVarFun r k
    | null ts && not (isQualified c)
    = return $ VariablePattern spi () $ renameIdent (unqualify c) k -- (varIdent r) k
    | otherwise = do
      let n = arity r
      checkFuncPatsExtension (spanInfo2Pos p)
      checkFuncPatCall r c
      ts' <- mapM (checkPattern p) ts
      mapM_ (checkFPTerm p) ts'
      return $ if n' > n
                 then let (ts1, ts2) = splitAt n ts'
                      in  genFuncPattAppl
                          (FunctionPattern spi () (qualVarIdent r) ts1) ts2
                 else FunctionPattern spi () (qualVarIdent r) ts'

checkInfixPattern :: SpanInfo -> SpanInfo -> Pattern () -> QualIdent -> Pattern ()
                  -> SCM (Pattern ())
checkInfixPattern p spi t1 op t2 = do
  m <- getModuleIdent
  env <- getRenameEnv
  case qualLookupVar op env of
    [Constr _ n] -> infixPattern op n
    [r]          -> funcPattern r op
    rs           -> case qualLookupVar (qualQualify m op) env of
      [Constr _ n] -> infixPattern (qualQualify m op) n
      [r]          -> funcPattern r (qualQualify m op)
      rs'          -> do if null rs && null rs'
                            then report $ errUndefinedData op
                            else report $ errAmbiguousData rs op
                         flip (InfixPattern spi ()) op <$> checkPattern p t1
                                                  <*> checkPattern p t2
  where
  infixPattern qop n = do
    when (n /= 2) $ report $ errWrongArity op n 2
    flip (InfixPattern spi ()) qop <$> checkPattern p t1 <*> checkPattern p t2
  funcPattern r qop = do
    checkFuncPatsExtension (spanInfo2Pos p)
    checkFuncPatCall r qop
    ts' <- mapM (checkPattern p) [t1,t2]
    let [t1',t2'] = ts'
    mapM_ (checkFPTerm p) ts'
    return $ InfixFuncPattern spi () t1' qop t2'

checkRecordPattern :: SpanInfo -> SpanInfo -> QualIdent -> [Field (Pattern ())]
                   -> SCM (Pattern ())
checkRecordPattern p spi c fs = do
  env <- getRenameEnv
  m   <- getModuleIdent
  case qualLookupVar c env of
    [Constr c' _] -> processRecPat (Just c') fs
    rs            -> case qualLookupVar (qualQualify m c) env of
      [Constr c' _] -> processRecPat (Just c') fs
      rs'           -> if null rs && null rs'
                          then do report $ errUndefinedData c
                                  processRecPat Nothing fs
                          else do report $ errAmbiguousData rs c
                                  processRecPat Nothing fs
  where
  processRecPat mcon fields = do
    fs' <- mapM (checkField (checkPattern p)) fields
    checkFieldLabels "pattern" p mcon fs'
    return $ RecordPattern spi () c fs'

checkFuncPatCall :: RenameInfo -> QualIdent -> SCM ()
checkFuncPatCall r f = case r of
  GlobalVar dep _ -> do
    addGlobalDep dep
    addFuncPat (dep @> f)
  _           -> report $ errFuncPatNotGlobal f

-- Note: process decls first
checkRhs :: Rhs () -> SCM (Rhs ())
checkRhs (SimpleRhs spi e ds) = inNestedScope $
  flip (SimpleRhs spi) <$> checkDeclGroup bindVarDecl ds <*> checkExpr spi e
checkRhs (GuardedRhs spi es ds) = inNestedScope $
  flip (GuardedRhs spi) <$> checkDeclGroup bindVarDecl ds <*> mapM checkCondExpr es

checkCondExpr :: CondExpr () -> SCM (CondExpr ())
checkCondExpr (CondExpr spi g e) =  CondExpr spi <$> checkExpr spi g <*> checkExpr spi e

checkExpr :: SpanInfo -> Expression () -> SCM (Expression ())
checkExpr _ (Literal       spi a l) = return $ Literal spi a l
checkExpr _ (Variable      spi a v) = checkVariable spi a v
checkExpr _ (Constructor   spi a c) = checkVariable spi a c
checkExpr p (Paren         spi   e) = Paren spi           <$> checkExpr p e
checkExpr p (Typed        spi e ty) = do
  checkImpredType ty
  flip (Typed spi) ty <$> checkExpr p e
checkExpr p (Record     spi _ c fs) = checkRecordExpr p spi c fs
checkExpr p (RecordUpdate spi e fs) = checkRecordUpdExpr p spi e fs
checkExpr p (Tuple        spi   es) = Tuple spi <$> mapM (checkExpr p) es
checkExpr p (List         spi a es) = List spi a <$> mapM (checkExpr p) es
checkExpr p (ListCompr    spi e qs) = withLocalEnv $ flip (ListCompr spi) <$>
  -- Note: must be flipped to insert qs into RenameEnv first
  mapM (checkStatement "list comprehension" p) qs <*> checkExpr p e
checkExpr p (EnumFrom              spi e) = EnumFrom spi <$> checkExpr p e
checkExpr p (EnumFromThen      spi e1 e2) =
  EnumFromThen spi <$> checkExpr p e1 <*> checkExpr p e2
checkExpr p (EnumFromTo        spi e1 e2) =
  EnumFromTo spi <$> checkExpr p e1 <*> checkExpr p e2
checkExpr p (EnumFromThenTo spi e1 e2 e3) =
  EnumFromThenTo spi <$> checkExpr p e1 <*> checkExpr p e2 <*> checkExpr p e3
checkExpr p (UnaryMinus            spi e) = UnaryMinus spi <$> checkExpr p e
checkExpr p (Apply             spi e1 e2) =
  Apply spi <$> checkExpr p e1 <*> checkExpr p e2
checkExpr p (InfixApply     spi e1 op e2) =
  InfixApply spi <$> checkExpr p e1 <*> checkOp op <*> checkExpr p e2
checkExpr p (LeftSection        spi e op) =
  LeftSection spi <$> checkExpr p e <*> checkOp op
checkExpr p (RightSection       spi op e) =
  RightSection spi <$> checkOp op <*> checkExpr p e
checkExpr p (Lambda             spi ts e) = inNestedScope $ checkLambda p spi ts e
checkExpr p (Let                spi ds e) = inNestedScope $
  Let spi <$> checkDeclGroup bindVarDecl ds <*> checkExpr p e
checkExpr p (Do                spi sts e) = withLocalEnv $
  Do spi <$> mapM (checkStatement "do sequence" p) sts <*> checkExpr p e
checkExpr p (IfThenElse     spi e1 e2 e3) =
  IfThenElse spi <$> checkExpr p e1 <*> checkExpr p e2 <*> checkExpr p e3
checkExpr p (Case          spi ct e alts) =
  Case spi ct <$> checkExpr p e <*> mapM checkAlt alts

checkLambda :: SpanInfo -> SpanInfo -> [Pattern ()] -> Expression ()
            -> SCM (Expression ())
checkLambda p spi ts e = case findMultiples (bvNoAnon ts) of
  []      -> do
    ts' <- mapM (bindPattern "lambda expression" p) ts
    Lambda spi ts' <$> checkExpr p e
  errVars -> do
    mapM_ (report . errDuplicateVariables) errVars
    let nubTs = nubBy (\t1 t2 -> (not . null) (on intersect bvNoAnon t1 t2)) ts
    mapM_ (bindPattern "lambda expression" p) nubTs
    Lambda spi ts <$> checkExpr p e
  where
    bvNoAnon t = filter (not . isAnonId) $ bv t

checkVariable :: SpanInfo -> a -> QualIdent -> SCM (Expression a)
checkVariable spi a v
    -- anonymous free variable
  | isAnonId (unqualify v) = do
    checkAnonFreeVarsExtension $ getPosition v
    (\n -> Variable spi a $ updQualIdent id (flip renameIdent n) v) <$> newId
    -- return $ Variable v
    -- normal variable
  | otherwise             = do
    env <- getRenameEnv
    case qualLookupVar v env of
      []              -> do report $ errUndefinedVariable v
                            return $ Variable spi a v
      [Constr    _ _]   -> return $ Constructor spi a v
      [GlobalVar f _]   -> addGlobalDep f >> return (Variable spi a v)
      [LocalVar v' _]   -> return $ Variable spi a $ qualify v' @> v
      [RecordLabel _ _] -> return $ Variable spi a v
      rs -> do
        m <- getModuleIdent
        case qualLookupVar (qualQualify m v) env of
          []              -> do report $ errAmbiguousIdent rs v
                                return $ Variable spi a v
          [Constr    _ _]   -> return $ Constructor spi a v
          [GlobalVar f _]   -> addGlobalDep f >> return (Variable spi a v)
          [LocalVar v' _]   -> return $ Variable spi a $ qualify v' @> v
          [RecordLabel _ _] -> return $ Variable spi a v
          rs'               -> do report $ errAmbiguousIdent rs' v
                                  return $ Variable spi a v

checkRecordExpr :: SpanInfo -> SpanInfo -> QualIdent -> [Field (Expression ())]
                -> SCM (Expression ())
checkRecordExpr _ spi c [] = do
  m   <- getModuleIdent
  env <- getRenameEnv
  case qualLookupVar c env of
    [Constr _ _] -> return $ Record spi () c []
    rs           -> case qualLookupVar (qualQualify m c) env of
      [Constr _ _] -> return $ Record spi () c []
      rs'          -> if null rs && null rs'
                         then do report $ errUndefinedData c
                                 return $ Record spi () c []
                         else do report $ errAmbiguousData rs c
                                 return $ Record spi () c []
checkRecordExpr p spi c fs =
  checkExpr p (RecordUpdate spi (Constructor (getSpanInfo c) () c)
                fs)

checkRecordUpdExpr :: SpanInfo -> SpanInfo -> Expression ()
                   -> [Field (Expression ())] -> SCM (Expression ())
checkRecordUpdExpr p spi e fs = do
  e'  <- checkExpr p e
  fs' <- mapM (checkField (checkExpr p)) fs
  case e' of
    Constructor _ a c -> do checkFieldLabels "construction" p (Just c) fs'
                            return $ Record spi a c fs'
    _                 -> do checkFieldLabels "update" p Nothing fs'
                            return $ RecordUpdate spi e' fs'

-- * Because patterns or decls eventually introduce new variables, the
--   scope has to be nested one level.
-- * Because statements are processed list-wise, inNestedEnv can not be
--   used as this nesting must be visible to following statements.
checkStatement :: String -> SpanInfo -> Statement () -> SCM (Statement ())
checkStatement _ p (StmtExpr spi   e) = StmtExpr spi <$> checkExpr p e
checkStatement s p (StmtBind spi t e) =
  flip (StmtBind spi) <$> checkExpr p e <*> (incNesting >> bindPattern s p t)
checkStatement _ _ (StmtDecl spi  ds) =
  StmtDecl spi <$> (incNesting >> checkDeclGroup bindVarDecl ds)

bindPattern :: String -> SpanInfo -> Pattern () -> SCM (Pattern ())
bindPattern s p t = do
  t' <- checkPattern p t
  banFPTerm s p t'
  addBoundVariables True t'

banFPTerm :: String -> SpanInfo -> Pattern a -> SCM ()
banFPTerm _ _ (LiteralPattern           _ _ _) = ok
banFPTerm _ _ (NegativePattern          _ _ _) = ok
banFPTerm _ _ (VariablePattern          _ _ _) = ok
banFPTerm s p (ConstructorPattern    _ _ _ ts) = mapM_ (banFPTerm s p) ts
banFPTerm s p (InfixPattern       _ _ t1 _ t2) = mapM_ (banFPTerm s p) [t1, t2]
banFPTerm s p (ParenPattern               _ t) = banFPTerm s p t
banFPTerm s p (RecordPattern         _ _ _ fs) = mapM_ banFPTermField fs
  where banFPTermField (Field _ _ x) = banFPTerm s p x
banFPTerm s p (TuplePattern              _ ts) = mapM_ (banFPTerm s p) ts
banFPTerm s p (ListPattern             _ _ ts) = mapM_ (banFPTerm s p) ts
banFPTerm s p (AsPattern                _ _ t) = banFPTerm s p t
banFPTerm s p (LazyPattern                _ t) = banFPTerm s p t
banFPTerm s p pat@(FunctionPattern    _ _ _ _)
 = report $ errUnsupportedFuncPattern s (spanInfo2Pos p) pat
banFPTerm s p pat@(InfixFuncPattern _ _ _ _ _)
 = report $ errUnsupportedFuncPattern s (spanInfo2Pos p) pat

checkOp :: InfixOp a -> SCM (InfixOp a)
checkOp op = do
  env <- getRenameEnv
  case qualLookupVar v env of
    []              -> report (errUndefinedVariable v) >> return op
    [Constr _ _]    -> return $ InfixConstr a v
    [GlobalVar f _] -> addGlobalDep f >> return (InfixOp a v)
    [LocalVar v' _] -> return $ InfixOp a $ qualify v'
    rs              -> do
      m <- getModuleIdent
      case qualLookupVar (qualQualify m v) env of
        []              -> report (errAmbiguousIdent rs v) >> return op
        [Constr _ _]    -> return $ InfixConstr a v
        [GlobalVar f _] -> addGlobalDep f >> return (InfixOp a v)
        [LocalVar v' _] -> return $ InfixOp a $ qualify v'
        rs'             -> report (errAmbiguousIdent rs' v) >> return op
  where v = opName op
        a = opAnnotation op

checkAlt :: Alt () -> SCM (Alt ())
checkAlt (Alt spi t rhs) = inNestedScope $
  Alt spi <$> bindPattern "case expression" spi t <*> checkRhs rhs

addBoundVariables :: (QuantExpr t) => Bool -> t -> SCM t
addBoundVariables checkDuplicates ts = do
  when checkDuplicates $ mapM_ (report . errDuplicateVariables)
                               (findMultiples bvs)
  modifyRenameEnv $ \ env -> foldr bindVar env (nub bvs)
  return ts
  where bvs = bv ts

-- For record patterns and expressions the compiler checks that all field
-- labels belong to the pattern or expression's constructor. For record
-- update expressions, the compiler checks that there is at least one
-- constructor which has all the specified field labels. In addition, the
-- compiler always checks that no field label occurs twice. Field labels
-- are always looked up in the global environment since they cannot be
-- shadowed by local variables (cf.\ Sect.~3.15.1 of the revised
-- Haskell'98 report~\cite{PeytonJones03:Haskell}).

checkFieldLabels :: String -> SpanInfo -> Maybe QualIdent -> [Field a] -> SCM ()
checkFieldLabels what p c fs = do
  mapM checkFieldLabel ls' >>= checkLabels p c ls'
  onJust (report . errDuplicateLabel what) (findDouble ls)
  where ls  = [l | Field _ l _ <- fs]
        ls' = nub ls
        onJust = maybe ok

checkFieldLabel :: QualIdent -> SCM [QualIdent]
checkFieldLabel l = do
  m   <- getModuleIdent
  env <- getRenameEnv
  case qualLookupVar l env of
    [RecordLabel _ cs] -> processLabel cs
    rs                 -> case qualLookupVar (qualQualify m l) env of
      [RecordLabel _ cs] -> processLabel cs
      rs'                -> if (null rs && null rs')
                               then do report $ errUndefinedLabel l
                                       return []
                               else do report $
                                         errAmbiguousIdent rs (qualQualify m l)
                                       return []
  where
  processLabel cs' = do
    when (null cs') $ report $ errUndefinedLabel l
    return cs'

checkLabels :: SpanInfo -> Maybe QualIdent -> [QualIdent] -> [[QualIdent]]
            -> SCM ()
checkLabels _ (Just c) ls css = do
  env <- getRenameEnv
  case qualLookupVar c env of
    [Constr c' _] -> mapM_ (report . errNoLabel c)
                           [l | (l, cs) <- zip ls css, c' `notElem` cs]
    _             -> internalError $
                       "Checks.SyntaxCheck.checkLabels: " ++ show c
checkLabels p Nothing ls css =
  when (null (foldr1 intersect css))
    $ report $ errNoCommonCons (spanInfo2Pos p) ls

checkField :: (a -> SCM a) -> Field a -> SCM (Field a)
checkField check (Field p l x) = Field p l <$> check x

-- -----------------------------------------------------------------------------
-- Impredicative polymorphism detection
-- -----------------------------------------------------------------------------

checkImpredDecl :: Decl a -> SCM ()
checkImpredDecl (DataDecl _ _ _ cs _)      = mapM_ checkImpredConsDecl cs
checkImpredDecl (NewtypeDecl _ _ _ c _)    = checkImpredNewConsDecl c
checkImpredDecl (TypeDecl _ _ _ ty)        = checkImpredType ty
checkImpredDecl (TypeSig _ _ ty)           = checkImpredType ty
checkImpredDecl (DefaultDecl _ tys)        = mapM_ checkImpredType tys
checkImpredDecl (ClassDecl _ _ _ _ ds)     = mapM_ checkImpredDecl ds
checkImpredDecl (InstanceDecl _ _ _ ty ds) = do
  checkImpredType ty
  mapM_ checkImpredDecl ds
checkImpredDecl _                          = ok

checkImpredConsDecl :: ConstrDecl -> SCM ()
checkImpredConsDecl (ConstrDecl _ _ tys)    = mapM_ checkImpredType tys
checkImpredConsDecl (ConOpDecl _ ty1 _ ty2) = mapM_ checkImpredType [ty1, ty2]
checkImpredConsDecl (RecordDecl _ _ fs)     = mapM_ checkImpredFieldDecl fs

checkImpredFieldDecl :: FieldDecl -> SCM ()
checkImpredFieldDecl (FieldDecl _ _ ty) = checkImpredType ty

checkImpredNewConsDecl :: NewConstrDecl -> SCM ()
checkImpredNewConsDecl (NewConstrDecl _ _ ty)      = checkImpredType ty
checkImpredNewConsDecl (NewRecordDecl _ _ (_, ty)) = checkImpredType ty

-- | Checks whether the type expression contains no impredicative polymorphism.
checkImpredType :: TypeExpr -> SCM ()
checkImpredType (ConstructorType _ _)      = ok
checkImpredType te@(ApplyType spi ty1 ty2) = do
  unlessM (checkImpredPoly ty2) $ do
    report $ errIllegalPolymorphicType (getPosition spi) te
  checkImpredType ty1
  checkImpredType ty2
checkImpredType (VariableType _ _)         = ok
checkImpredType te@(TupleType spi tys)     = do
  unlessM (allM checkImpredPoly tys) $ do
    report $ errIllegalPolymorphicType (getPosition spi) te
  mapM_ checkImpredType tys
checkImpredType te@(ListType spi ty)       = do
  unlessM (checkImpredPoly ty) $ do
    report $ errIllegalPolymorphicType (getPosition spi) te
  checkImpredType ty
checkImpredType (ArrowType _ ty1 ty2)      = do
  checkImpredType ty1
  checkImpredType ty2
checkImpredType (ParenType _ ty)           = checkImpredType ty
checkImpredType (ContextType _ _ ty)       = checkImpredType ty
checkImpredType (ForallType _ _ ty)        = checkImpredType ty

-- | Checks whether the given type expression contains no universally
-- quantified type variables.
checkImpredPoly :: TypeExpr -> SCM Bool
checkImpredPoly (ConstructorType _ tc) = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo tc tcEnv of
    [AliasType _ _ _ ty] -> checkImpredPoly (fromType identSupply ty)
    _ -> case qualLookupTypeInfo (qualQualify m tc) tcEnv of
           [AliasType _ _ _ ty] -> checkImpredPoly (fromType identSupply ty)
           _                    -> return True
checkImpredPoly (ApplyType _ ty1 ty2)  = allM checkImpredPoly [ty1, ty2]
checkImpredPoly (VariableType _ _)     = return True
checkImpredPoly (TupleType _ tys)      = allM checkImpredPoly tys
checkImpredPoly (ListType _ ty)        = checkImpredPoly ty
checkImpredPoly (ArrowType _ ty1 ty2)  = allM checkImpredPoly [ty1, ty2]
checkImpredPoly (ParenType _ ty)       = checkImpredPoly ty
checkImpredPoly (ContextType _ _ _)    = return False
checkImpredPoly (ForallType _ _ _)     = return False

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

constrs :: Decl a -> [Ident]
constrs (DataDecl    _ _ _ cs _) = map constrId cs
constrs (NewtypeDecl _ _ _ nc _) = [nconstrId nc]
constrs _                        = []

vars :: Decl a -> [Ident]
vars (TypeSig          _ fs _) = fs
vars (FunctionDecl    _ _ f _) = [f]
vars (ExternalDecl       _ vs) = bv vs
vars (PatternDecl       _ t _) = bv t
vars (FreeDecl           _ vs) = bv vs
vars _                         = []

recLabels :: Decl a -> [Ident]
recLabels (DataDecl    _ _ _ cs _) = concatMap recordLabels cs
recLabels (NewtypeDecl _ _ _ nc _) = nrecordLabels nc
recLabels _                        = []

-- Since the compiler expects all rules of the same function to be together,
-- it is necessary to sort the list of declarations.

sortFuncDecls :: [Decl a] -> [Decl a]
sortFuncDecls decls = sortFD Set.empty [] decls
 where
 sortFD _   res []              = reverse res
 sortFD env res (decl : decls') = case decl of
   FunctionDecl _ _ ident _
    | ident `Set.member` env
    -> sortFD env (insertBy cmpFuncDecl decl res) decls'
    | otherwise
    -> sortFD (Set.insert ident env) (decl:res) decls'
   _    -> sortFD env (decl:res) decls'

cmpFuncDecl :: Decl a -> Decl a -> Ordering
cmpFuncDecl (FunctionDecl _ _ id1 _) (FunctionDecl _ _ id2 _)
   | id1 == id2 = EQ
   | otherwise  = GT
cmpFuncDecl _ _ = GT

-- Due to the lack of a capitalization convention in Curry, it is
-- possible that an identifier may ambiguously refer to a data
-- constructor and a function provided that both are imported from some
-- other module. When checking whether an identifier denotes a
-- constructor there are two options with regard to ambiguous
-- identifiers:
--   * Handle the identifier as a data constructor if at least one of
--     the imported names is a data constructor.
--   * Handle the identifier as a data constructor only if all imported
--     entities are data constructors.
-- We choose the first possibility here because in the second case a
-- redefinition of a constructor can magically become possible if a
-- function with the same name is imported. It seems better to warn
-- the user about the fact that the identifier is ambiguous.

isDataConstr :: Ident -> RenameEnv -> Bool
isDataConstr v = any isConstr . lookupVar v . globalEnv . toplevelEnv

isConstr :: RenameInfo -> Bool
isConstr (Constr      _ _) = True
isConstr (GlobalVar   _ _) = False
isConstr (LocalVar    _ _) = False
isConstr (RecordLabel _ _) = False

isLabel :: RenameInfo -> Bool
isLabel (Constr      _ _) = False
isLabel (GlobalVar   _ _) = False
isLabel (LocalVar    _ _) = False
isLabel (RecordLabel _ _) = True

-- varIdent :: RenameInfo -> Ident
-- varIdent (GlobalVar _ v) = unqualify v
-- varIdent (LocalVar  _ v) = v
-- varIdent _ = internalError "SyntaxCheck.varIdent: no variable"

qualVarIdent :: RenameInfo -> QualIdent
qualVarIdent (GlobalVar v _) = v
qualVarIdent (LocalVar  v _) = qualify v
qualVarIdent _ = internalError "SyntaxCheck.qualVarIdent: no variable"

arity :: RenameInfo -> Int
arity (Constr      _ n) = n
arity (GlobalVar   _ n) = n
arity (LocalVar    _ n) = n
arity (RecordLabel _ _) = 1

-- Unlike expressions, constructor terms have no possibility to represent
-- over-applications in functional patterns. Therefore it is necessary to
-- transform them to nested function patterns using the prelude function
-- apply. E.g., the function pattern (id id 10) is transformed to
-- (apply (id id) 10).

genFuncPattAppl :: Pattern () -> [Pattern ()] -> Pattern ()
genFuncPattAppl term []     = term
genFuncPattAppl term (t:ts)
   = FunctionPattern NoSpanInfo () qApplyId [genFuncPattAppl term ts, t] -- TODO FIXME major problem

checkFPTerm :: SpanInfo -> Pattern a -> SCM ()
checkFPTerm _ (LiteralPattern        _ _ _) = ok
checkFPTerm _ (NegativePattern       _ _ _) = ok
checkFPTerm _ (VariablePattern       _ _ _) = ok
checkFPTerm p (ConstructorPattern _ _ _ ts) = mapM_ (checkFPTerm p) ts
checkFPTerm p (InfixPattern    _ _ t1 _ t2) = mapM_ (checkFPTerm p) [t1, t2]
checkFPTerm p (ParenPattern            _ t) = checkFPTerm p t
checkFPTerm p (TuplePattern           _ ts) = mapM_ (checkFPTerm p) ts
checkFPTerm p (ListPattern          _ _ ts) = mapM_ (checkFPTerm p) ts
checkFPTerm p (AsPattern             _ _ t) = checkFPTerm p t
checkFPTerm p t@(LazyPattern           _ _) =
  report $ errUnsupportedFPTerm "Lazy" (spanInfo2Pos p) t
checkFPTerm p (RecordPattern      _ _ _ fs) = mapM_ (checkFPTerm p)
                                            [ t | Field _ _ t <- fs ]
checkFPTerm _ (FunctionPattern     _ _ _ _) = ok -- do not check again
checkFPTerm _ (InfixFuncPattern  _ _ _ _ _) = ok -- do not check again

-- ---------------------------------------------------------------------------
-- Miscellaneous functions
-- ---------------------------------------------------------------------------

checkFuncPatsExtension :: Position -> SCM ()
checkFuncPatsExtension p = checkUsedExtension p
  "Functional Patterns" FunctionalPatterns

checkAnonFreeVarsExtension :: Position -> SCM ()
checkAnonFreeVarsExtension p = checkUsedExtension p
  "Anonymous free variables" AnonFreeVars

checkUsedExtension :: Position -> String -> KnownExtension -> SCM ()
checkUsedExtension pos msg ext = do
  enabled <- hasExtension ext
  unless enabled $ do
    report $ errMissingLanguageExtension pos msg ext
    enableExtension ext -- to avoid multiple warnings

typeArity :: TypeExpr -> Int
typeArity (ArrowType _ _ t2) = 1 + typeArity t2
typeArity _                  = 0

getFlatLhs :: Equation a -> (Ident, [Pattern a])
getFlatLhs (Equation  _ lhs _) = flatLhs lhs

opAnnotation :: InfixOp a -> a
opAnnotation (InfixOp     a _) = a
opAnnotation (InfixConstr a _) = a

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errUnsupportedFPTerm :: String -> Position -> Pattern a -> Message
errUnsupportedFPTerm s p pat = posMessage p $ text s
  <+> text "patterns are not supported inside a functional pattern."
  $+$ ppPattern 0 pat

errUnsupportedFuncPattern :: String -> Position -> Pattern a -> Message
errUnsupportedFuncPattern s p pat = posMessage p $
  text "Functional patterns are not supported inside a" <+> text s <> dot
  $+$ ppPattern 0 pat

errFuncPatNotGlobal :: QualIdent -> Message
errFuncPatNotGlobal f = posMessage f $ hsep $ map text
  ["Function", escQualName f, "in functional pattern is not global"]

errFuncPatCyclic :: QualIdent -> QualIdent -> Message
errFuncPatCyclic fp f = posMessage fp $ hsep $ map text
  [ "Function", escName $ unqualify fp, "used in functional pattern depends on"
  , escName $ unqualify f, " causing a cyclic dependency"]

errPrecedenceOutOfRange :: Position -> Integer -> Message
errPrecedenceOutOfRange p i = posMessage p $ hsep $ map text
  ["Precedence out of range:", show i]

errUndefinedVariable :: QualIdent -> Message
errUndefinedVariable v = posMessage v $ hsep $ map text
  [escQualName v, "is undefined"]

errUndefinedData :: QualIdent -> Message
errUndefinedData c = posMessage c $ hsep $ map text
  ["Undefined data constructor", escQualName c]

errUndefinedLabel :: QualIdent -> Message
errUndefinedLabel l = posMessage l $  hsep $ map text
  ["Undefined record label", escQualName l]

errUndefinedMethod :: QualIdent -> Ident -> Message
errUndefinedMethod qcls f = posMessage f $ hsep $ map text
  [escName f, "is not a (visible) method of class", escQualName qcls]

errAmbiguousIdent :: [RenameInfo] -> QualIdent -> Message
errAmbiguousIdent rs qn | any isConstr rs = errAmbiguousData rs qn
                        | any isLabel  rs = errAmbiguousLabel rs qn
                        | otherwise       = errAmbiguous "variable" rs qn

errAmbiguousData :: [RenameInfo] -> QualIdent -> Message
errAmbiguousData = errAmbiguous "data constructor"

errAmbiguousLabel :: [RenameInfo] -> QualIdent -> Message
errAmbiguousLabel = errAmbiguous "field label"

errAmbiguous :: String -> [RenameInfo] -> QualIdent -> Message
errAmbiguous what rs qn = posMessage qn
  $   text "Ambiguous" <+> text what <+> text (escQualName qn)
  $+$ text "It could refer to:"
  $+$ nest 2 (vcat (map ppRenameInfo rs))

errDuplicateDefinition :: Ident -> Message
errDuplicateDefinition v = posMessage v $ hsep $ map text
  ["More than one definition for", escName v]

errDuplicateVariables :: [Ident] -> Message
errDuplicateVariables [] = internalError
  "SyntaxCheck.errDuplicateVariables: empty list"
errDuplicateVariables (v:vs) = posMessage v $
  text (escName v) <+> text "occurs more than one in pattern at:" $+$
  nest 2 (vcat (map (ppPosition . getPosition) (v:vs)))

errMultipleDataConstructor :: [Ident] -> Message
errMultipleDataConstructor [] = internalError
  "SyntaxCheck.errMultipleDataDeclaration: empty list"
errMultipleDataConstructor (i:is) = posMessage i $
  text "Multiple definitions for data/record constructor" <+> text (escName i)
  <+> text "at:" $+$
  nest 2 (vcat (map (ppPosition . getPosition) (i:is)))

errMultipleDeclarations :: ModuleIdent -> [Ident] -> Message
errMultipleDeclarations _ [] = internalError
  "SyntaxCheck.errMultipleDeclarations: empty list"
errMultipleDeclarations m (i:is) = posMessage i $
  text "Multiple declarations of" <+> text (escQualName (qualifyWith m i))
  $+$ text "Declared at:" $+$
  nest 2 (vcat (map (ppPosition . getPosition) (i:is)))

errDuplicateTypeSig :: [Ident] -> Message
errDuplicateTypeSig [] = internalError
  "SyntaxCheck.errDuplicateTypeSig: empty list"
errDuplicateTypeSig (v:vs) = posMessage v $
  text "More than one type signature for" <+> text (escName v)
  <+> text "at:" $+$
  nest 2 (vcat (map (ppPosition . getPosition) (v:vs)))

errDuplicateLabel :: String -> QualIdent -> Message
errDuplicateLabel what l = posMessage l $ hsep $ map text
  ["Field label", escQualName l, "occurs more than once in record", what]

errNonVariable :: String -> Ident -> Message
errNonVariable what c = posMessage c $ hsep $ map text
  ["Data constructor", escName c, "in left hand side of", what]

errNoBody :: Ident -> Message
errNoBody v = posMessage v $  hsep $ map text ["No body for", escName v]

errNoCommonCons :: Position -> [QualIdent] -> Message
errNoCommonCons p ls = posMessage p $
  text "No constructor has all of these fields:"
  $+$ nest 2 (vcat (map (text . escQualName) ls))

errNoLabel :: QualIdent -> QualIdent -> Message
errNoLabel c l = posMessage l $ hsep $ map text
  [escQualName l, "is not a field label of constructor", escQualName c]

errNoTypeSig :: Ident -> Message
errNoTypeSig f = posMessage f $ hsep $ map text
  ["No type signature for external function", escName f]

errToplevelPattern :: Position -> Message
errToplevelPattern p = posMessage p $ text
  "Pattern declaration not allowed at top-level"

errDifferentArity :: [Ident] -> Message
errDifferentArity [] = internalError
  "SyntaxCheck.errDifferentArity: empty list"
errDifferentArity (i:is) = posMessage i $
  text "Equations for" <+> text (escName i) <+> text "have different arities"
  <+> text "at:" $+$
  nest 2 (vcat (map (ppPosition . getPosition) (i:is)))

errWrongArity :: QualIdent -> Int -> Int -> Message
errWrongArity c arity' argc = posMessage c $ hsep (map text
  ["Data constructor", escQualName c, "expects", arguments arity'])
  <> comma <+> text "but is applied to" <+> text (show argc)
  where arguments 0 = "no arguments"
        arguments 1 = "1 argument"
        arguments n = show n ++ " arguments"

errMissingLanguageExtension :: Position -> String -> KnownExtension -> Message
errMissingLanguageExtension p what ext = posMessage p $
  text what <+> text "are not supported in standard Curry." $+$
  nest 2 (text "Use flag or -X" <+> text (show ext)
          <+> text "to enable this extension.")

errInfixWithoutParens :: Position -> [(QualIdent, QualIdent)] -> Message
errInfixWithoutParens p calls = posMessage p $
  text "Missing parens in infix patterns:" $+$
  vcat (map showCall calls)
  where
  showCall (q1, q2) = showWithPos q1 <+> text "calls" <+> showWithPos q2
  showWithPos q =  text (qualName q)
               <+> parens (text $ showLine $ getPosition q)

errIllegalPolymorphicType :: Position -> TypeExpr -> Message
errIllegalPolymorphicType p ty = posMessage p $ vcat
  [ text "Illegal polymorphic type" <+> ppTypeExpr 0 ty
  , text "Impredicative polymorphism isn't yet supported."
  ]
