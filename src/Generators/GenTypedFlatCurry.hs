{- |
    Module      :  $Header$
    Description :  Generation of typed FlatCurry program terms
    Copyright   :  (c) 2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of a typed 'FlatCurry' program term
    for a given module in the intermediate language.
-}
{-# LANGUAGE CPP #-}
module Generators.GenTypedFlatCurry (genTypedFlatCurry) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Monad              ((<=<))
import           Control.Monad.Extra        (concatMapM)
import qualified Control.Monad.State as S   ( State, evalState, get, gets
                                            , modify, put )
import           Data.Function              (on)
import           Data.List                  (nub, sortBy)
import           Data.Maybe                 (fromMaybe)
import qualified Data.Map            as Map (Map, empty, insert, lookup)
import qualified Data.Set            as Set (Set, empty, insert, member)

import           Curry.Base.Ident
import           Curry.FlatCurry.Typed.Goodies (typeName)
import           Curry.FlatCurry.Typed.Type
import qualified Curry.Syntax as CS

import Base.CurryTypes     (toType)
import Base.Messages       (internalError)
import Base.NestEnv        ( NestEnv, emptyEnv, bindNestEnv, lookupNestEnv
                           , nestEnv, unnestEnv )
import Base.TypeExpansion
import Base.Types

import CompilerEnv
import Env.OpPrec          (mkPrec)
import Env.TypeConstructor (TCEnv)
import Env.Value           (ValueEnv, ValueInfo (..), qualLookupValue)

import qualified IL
import Transformations     (transType)

-- transforms intermediate language code (IL) to typed FlatCurry code
genTypedFlatCurry :: CompilerEnv -> CS.Module Type -> IL.Module
                  -> TProg
genTypedFlatCurry env mdl il = patchPrelude $ run env mdl (trModule il)

-- -----------------------------------------------------------------------------
-- Addition of primitive types for lists and tuples to the Prelude
-- -----------------------------------------------------------------------------

patchPrelude :: TProg -> TProg
patchPrelude p@(TProg n _ ts fs os)
  | n == prelude = TProg n [] ts' fs os
  | otherwise    = p
  where ts' = sortBy (compare `on` typeName) pts
        pts = primTypes ++ ts

primTypes :: [TypeDecl]
primTypes =
  [ Type arrow Public [0, 1] []
  , Type unit Public [] [(Cons unit 0 Public [])]
  , Type nil Public [0] [ Cons nil  0 Public []
                        , Cons cons 2 Public [TVar 0, TCons nil [TVar 0]]
                        ]
  ] ++ map mkTupleType [2 .. maxTupleArity]
  where arrow = mkPreludeQName "(->)"
        unit  = mkPreludeQName "()"
        nil   = mkPreludeQName "[]"
        cons  = mkPreludeQName ":"

mkTupleType :: Int -> TypeDecl
mkTupleType arity = Type tuple Public [0 .. arity - 1]
  [Cons tuple arity Public (map TVar [0 .. arity - 1])]
  where tuple = mkPreludeQName $ '(' : replicate (arity - 1) ',' ++ ")"

mkPreludeQName :: String -> QName
mkPreludeQName n = (prelude, n)

prelude :: String
prelude = "Prelude"

-- |Maximal arity of tuples
maxTupleArity :: Int
maxTupleArity = 15

-- -----------------------------------------------------------------------------

-- The environment 'FlatEnv' is embedded in the monadic representation
-- 'FlatState' which allows the usage of 'do' expressions.
type FlatState a = S.State FlatEnv a

-- Data type for representing an environment which contains information needed
-- for generating FlatCurry code.
data FlatEnv = FlatEnv
  { modIdent     :: ModuleIdent      -- current module
  -- for visibility calculation
  , tyExports    :: Set.Set Ident    -- exported types
  , valExports   :: Set.Set Ident    -- exported values (functions + constructors)
  , tcEnv        :: TCEnv            -- type constructor environment
  , tyEnv        :: ValueEnv         -- type environment
  , fixities     :: [CS.IDecl]       -- fixity declarations
  , typeSynonyms :: [CS.Decl Type]   -- type synonyms
  , imports      :: [ModuleIdent]    -- module imports
  -- state for mapping identifiers to indexes
  , nextVar      :: Int              -- fresh variable index counter
  , varMap       :: NestEnv VarIndex -- map of identifier to variable index
  }

-- Runs a 'FlatState' action and returns the result
run :: CompilerEnv -> CS.Module Type -> FlatState a -> a
run env (CS.Module _ mid es is ds) act = S.evalState act env0
  where
  es'  = case es of Just (CS.Exporting _ e) -> e
                    _                       -> []
  env0 = FlatEnv
    { modIdent     = mid
     -- for visibility calculation
    , tyExports  = foldr (buildTypeExports  mid) Set.empty es'
    , valExports = foldr (buildValueExports mid) Set.empty es'
    -- This includes *all* imports, even unused ones
    , imports      = nub [ m | CS.ImportDecl _ m _ _ _ <- is ]
    -- Environment to retrieve the type of identifiers
    , tyEnv        = valueEnv env
    , tcEnv        = tyConsEnv env
    -- Fixity declarations
    , fixities     = [ CS.IInfixDecl p fix (mkPrec mPrec) (qualifyWith mid o)
                     | CS.InfixDecl p fix mPrec os <- ds, o <- os
                     ]
    -- Type synonyms in the module
    , typeSynonyms = [ d | d@CS.TypeDecl{} <- ds ]
    , nextVar      = 0
    , varMap       = emptyEnv
    }

-- Builds a table containing all exported identifiers from a module.
buildTypeExports :: ModuleIdent -> CS.Export -> Set.Set Ident -> Set.Set Ident
buildTypeExports mid (CS.ExportTypeWith tc _)
  | isLocalIdent mid tc = Set.insert (unqualify tc)
buildTypeExports _   _  = id

-- Builds a table containing all exported identifiers from a module.
buildValueExports :: ModuleIdent -> CS.Export -> Set.Set Ident -> Set.Set Ident
buildValueExports mid (CS.Export             q)
  | isLocalIdent mid q  = Set.insert (unqualify q)
buildValueExports mid (CS.ExportTypeWith tc cs)
  | isLocalIdent mid tc = flip (foldr Set.insert) cs
buildValueExports _   _  = id

getModuleIdent :: FlatState ModuleIdent
getModuleIdent = S.gets modIdent

getArity :: QualIdent -> FlatState Int
getArity qid = S.gets tyEnv >>= \ env -> return $ case qualLookupValue qid env of
  [DataConstructor  _ a _ _] -> a
  [NewtypeConstructor _ _ _] -> 1
  [Value            _ _ a _] -> a
  [Label              _ _ _] -> 1
  _                          -> internalError
                                ("GenTypedFlatCurry.getArity: " ++ qualName qid)

getFixities :: FlatState [CS.IDecl]
getFixities = S.gets fixities

-- The function 'typeSynonyms' returns the list of type synonyms.
getTypeSynonyms :: FlatState [CS.Decl Type]
getTypeSynonyms = S.gets typeSynonyms

-- Retrieve imports
getImports :: [ModuleIdent] -> FlatState [String]
getImports imps = (nub . map moduleName . (imps ++)) <$> S.gets imports

-- -----------------------------------------------------------------------------
-- Stateful part, used for translation of rules and expressions
-- -----------------------------------------------------------------------------

-- resets var index and environment
withFreshEnv :: FlatState a -> FlatState a
withFreshEnv act = S.modify (\ s -> s { nextVar = 0, varMap = emptyEnv }) >> act

-- Execute an action in a nested variable mapping
inNestedEnv :: FlatState a -> FlatState a
inNestedEnv act = do
  S.modify $ \ s -> s { varMap = nestEnv   $ varMap s }
  res <- act
  S.modify $ \ s -> s { varMap = unnestEnv $ varMap s }
  return res

-- Generates a new variable index for an identifier
newVar :: IL.Type -> Ident -> FlatState (VarIndex, TypeExpr)
newVar ty i = do
  idx <- (+1) <$> S.gets nextVar
  S.modify $ \ s -> s { nextVar = idx, varMap = bindNestEnv i idx (varMap s) }
  ty' <- trType ty
  return (idx, ty')

-- Retrieve the variable index assigned to an identifier
getVarIndex :: Ident -> FlatState VarIndex
getVarIndex i = S.gets varMap >>= \ varEnv -> case lookupNestEnv i varEnv of
  [v] -> return v
  _   -> internalError $ "GenFlatCurry.getVarIndex: " ++ escName i

-- -----------------------------------------------------------------------------
-- Translation of an interface
-- -----------------------------------------------------------------------------

-- Translate an operator declaration
trIOpDecl :: CS.IDecl -> FlatState [OpDecl]
trIOpDecl (CS.IInfixDecl _ fix prec op)
  = (\op' -> [Op op' (cvFixity fix) prec]) <$> trQualIdent op
trIOpDecl _ = return []

-- -----------------------------------------------------------------------------
-- Translation of a module
-- -----------------------------------------------------------------------------

trModule :: IL.Module -> FlatState TProg
trModule (IL.Module mid is ds) = do
  is' <- getImports is
  sns <- getTypeSynonyms >>= concatMapM trTypeSynonym
  tds <- concatMapM trTypeDecl ds
  fds <- concatMapM (return . map runNormalization <=< trTFuncDecl) ds
  ops <- getFixities >>= concatMapM trIOpDecl
  return $ TProg (moduleName mid) is' (sns ++ tds) fds ops

-- Translate a type synonym
trTypeSynonym :: CS.Decl a -> FlatState [TypeDecl]
trTypeSynonym (CS.TypeDecl _ t tvs ty) = do
  m    <- getModuleIdent
  qid  <- flip qualifyWith t <$> getModuleIdent
  t'   <- trQualIdent qid
  vis  <- getTypeVisibility qid
  tEnv <- S.gets tcEnv
  ty'  <- trType (transType $ expandType m tEnv $ toType tvs ty)
  return [TypeSyn t' vis [0 .. length tvs - 1] ty']
trTypeSynonym _                        = return []

-- Translate a data declaration
-- For empty data declarations, an additional constructor is generated. This
-- is due to the fact that external data declarations are translated into data
-- declarations with zero constructors and without the additional constructor
-- empty data declarations could not be distinguished from external ones.
trTypeDecl :: IL.Decl -> FlatState [TypeDecl]
trTypeDecl (IL.DataDecl      qid a []) = do
  q'  <- trQualIdent qid
  vis <- getTypeVisibility qid
  c   <- trQualIdent $ qualify (mkIdent $ "_Constr#" ++ idName (unqualify qid))
  let tvs = [0 .. a - 1]
  return [Type q' vis tvs [Cons c 1 Private [TCons q' $ map TVar tvs]]]
trTypeDecl (IL.DataDecl      qid a cs) = do
  q'  <- trQualIdent qid
  vis <- getTypeVisibility qid
  cs' <- mapM trConstrDecl cs
  return [Type q' vis [0 .. a - 1] cs']
trTypeDecl (IL.ExternalDataDecl qid a) = do
  q'  <- trQualIdent qid
  vis <- getTypeVisibility qid
  return [Type q' vis [0 .. a - 1] []]
trTypeDecl _                           = return []

-- Translate a constructor declaration
trConstrDecl :: IL.ConstrDecl -> FlatState ConsDecl
trConstrDecl (IL.ConstrDecl qid tys) = flip Cons (length tys)
  <$> trQualIdent qid
  <*> getVisibility qid
  <*> mapM trType tys

-- Translate a type expression
trType :: IL.Type -> FlatState TypeExpr
trType (IL.TypeConstructor t tys) = TCons <$> trQualIdent t <*> mapM trType tys
trType (IL.TypeVariable      idx) = return $ TVar $ abs idx
trType (IL.TypeArrow     ty1 ty2) = FuncType <$> trType ty1 <*> trType ty2
trType (IL.TypeForall    idxs ty) = ForallType (map abs idxs) <$> trType ty

-- Convert a fixity
cvFixity :: CS.Infix -> Fixity
cvFixity CS.InfixL = InfixlOp
cvFixity CS.InfixR = InfixrOp
cvFixity CS.Infix  = InfixOp

-- -----------------------------------------------------------------------------
-- Function declarations
-- -----------------------------------------------------------------------------

-- Translate a function declaration
trTFuncDecl :: IL.Decl -> FlatState [TFuncDecl]
trTFuncDecl (IL.FunctionDecl f vs _ e) = do
  f'  <- trQualIdent f
  a   <- getArity f
  vis <- getVisibility f
  ty' <- trType ty
  r'  <- trTRule vs e
  return [TFunc f' a vis ty' r']
  where ty = foldr IL.TypeArrow (IL.typeOf e) $ map fst vs
trTFuncDecl (IL.ExternalDecl     f ty) = do
  f'   <- trQualIdent f
  a    <- getArity f
  vis  <- getVisibility f
  ty'  <- trType ty
  r'   <- trTExternal ty f
  return [TFunc f' a vis ty' r']
trTFuncDecl _                           = return []

-- Translate a function rule.
-- Resets variable index so that for every rule variables start with index 1
trTRule :: [(IL.Type, Ident)] -> IL.Expression
        -> FlatState TRule
trTRule vs e = withFreshEnv $ TRule <$> mapM (uncurry newVar) vs
                                    <*> trTExpr e

trTExternal :: IL.Type -> QualIdent -> FlatState TRule
trTExternal ty f = flip TExternal (qualName f) <$> trType ty

-- Translate an expression
trTExpr :: IL.Expression -> FlatState TExpr
trTExpr (IL.Literal       ty l) = TLit  <$> trType ty <*> trLiteral l
trTExpr (IL.Variable      ty v) = TVarE <$> trType ty <*> getVarIndex v
trTExpr (IL.Function    ty f _) = genCall Fun ty f []
trTExpr (IL.Constructor ty c _) = genCall Con ty c []
trTExpr (IL.Apply        e1 e2) = trApply e1 e2
trTExpr (IL.Case        t e bs) = TCase (cvEval t) <$> trTExpr e
                                  <*> mapM (inNestedEnv . trAlt) bs
trTExpr (IL.Or           e1 e2) = TOr <$> trTExpr e1 <*> trTExpr e2
trTExpr (IL.Exist       v ty e) = inNestedEnv $ do
  v' <- newVar ty v
  e' <- trTExpr e
  return $ case e' of TFree vs e'' -> TFree (v' : vs) e''
                      _            -> TFree (v' : []) e'
trTExpr (IL.Let (IL.Binding v b) e) = inNestedEnv $ do
  v' <- newVar (IL.typeOf b) v
  b' <- trTExpr b
  e' <- trTExpr e
  return $ case e' of TLet bs e'' -> TLet ((v', b'):bs) e''
                      _           -> TLet ((v', b'):[]) e'
trTExpr (IL.Letrec   bs e) = inNestedEnv $ do
  let (vs, es) = unzip [ ((IL.typeOf b, v), b) | IL.Binding v b <- bs]
  TLet <$> (zip <$> mapM (uncurry newVar) vs <*> mapM trTExpr es)
       <*> trTExpr e
trTExpr (IL.Typed e _) = TTyped <$> trTExpr e <*> ty'
  where ty' = trType $ IL.typeOf e

-- Translate a literal
trLiteral :: IL.Literal -> FlatState Literal
trLiteral (IL.Char  c) = return $ Charc  c
trLiteral (IL.Int   i) = return $ Intc   i
trLiteral (IL.Float f) = return $ Floatc f

-- Translate a higher-order application
trApply :: IL.Expression -> IL.Expression -> FlatState TExpr
trApply e1 e2 = genFlatApplic e1 [e2]
  where
  genFlatApplic e es = case e of
    IL.Apply        ea eb -> genFlatApplic ea (eb:es)
    IL.Function    ty f _ -> genCall Fun ty f es
    IL.Constructor ty c _ -> genCall Con ty c es
    _ -> do
      expr <- trTExpr e
      genApply expr es

-- Translate an alternative
trAlt :: IL.Alt -> FlatState TBranchExpr
trAlt (IL.Alt p e) = TBranch <$> trPat p <*> trTExpr e

-- Translate a pattern
trPat :: IL.ConstrTerm -> FlatState TPattern
trPat (IL.LiteralPattern        ty l) = TLPattern <$> trType ty <*> trLiteral l
trPat (IL.ConstructorPattern ty c vs) =
  TPattern <$> trType ty <*> trQualIdent c <*> mapM (uncurry newVar) vs
trPat (IL.VariablePattern        _ _) = internalError "GenTypedFlatCurry.trPat"

-- Convert a case type
cvEval :: IL.Eval -> CaseType
cvEval IL.Rigid = Rigid
cvEval IL.Flex  = Flex

data Call = Fun | Con

-- Generate a function or constructor call
genCall :: Call -> IL.Type -> QualIdent -> [IL.Expression]
        -> FlatState TExpr
genCall call ty f es = do
  f'    <- trQualIdent f
  arity <- getArity f
  case compare supplied arity of
    LT -> genTComb ty f' es (part call (arity - supplied))
    EQ -> genTComb ty f' es (full call)
    GT -> do
      let (es1, es2) = splitAt arity es
      funccall <- genTComb ty f' es1 (full call)
      genApply funccall es2
  where
  supplied = length es
  full Fun = FuncCall
  full Con = ConsCall
  part Fun = FuncPartCall
  part Con = ConsPartCall

genTComb :: IL.Type -> QName -> [IL.Expression] -> CombType -> FlatState TExpr
genTComb ty qid es ct = do
  ty' <- trType ty
  let ty'' = defunc ty' (length es)
  TComb ty'' ct qid <$> mapM trTExpr es
  where
  defunc t               0 = t
  defunc (FuncType _ t2) n = defunc t2 (n - 1)
  defunc _               _ = internalError "GenTypedFlatCurry.genTComb.defunc"

genApply :: TExpr -> [IL.Expression] -> FlatState TExpr
genApply e es = do
  ap  <- trQualIdent qApplyId
  es' <- mapM trTExpr es
  return $ foldl (\e1 e2 -> let FuncType _ ty2 = typeOf e1
                            in TComb ty2 FuncCall ap [e1, e2])
             e es'

-- -----------------------------------------------------------------------------
-- Normalization
-- -----------------------------------------------------------------------------

runNormalization :: Normalize a => a -> a
runNormalization x = S.evalState (normalize x) (0, Map.empty)

type NormState a = S.State (Int, Map.Map Int Int) a

class Normalize a where
  normalize :: a -> NormState a

instance Normalize Int where
  normalize i = do
    (n, m) <- S.get
    case Map.lookup i m of
      Nothing -> do
        S.put (n + 1, Map.insert i n m)
        return n
      Just n' -> return n'

instance Normalize TypeExpr where
  normalize (TVar           i) = TVar <$> normalize i
  normalize (TCons      q tys) = TCons q <$> mapM normalize tys
  normalize (FuncType ty1 ty2) = FuncType <$> normalize ty1 <*> normalize ty2
  normalize (ForallType is ty) =
    ForallType <$> mapM normalize is <*> normalize ty

instance Normalize b => Normalize (a, b) where
  normalize (x, y) = (,) x <$> normalize y

instance Normalize TFuncDecl where
  normalize (TFunc f a v ty r) = TFunc f a v <$> normalize ty <*> normalize r

instance Normalize TRule where
  normalize (TRule        vs e) = TRule <$> mapM normalize vs
                                        <*> normalize e
  normalize (TExternal ty    s) = flip TExternal s <$> normalize ty

instance Normalize TExpr where
  normalize (TVarE  ty       v) = flip TVarE  v <$> normalize ty
  normalize (TLit   ty       l) = flip TLit  l  <$> normalize ty
  normalize (TComb  ty ct f es) = flip TComb ct <$> normalize ty
                                                <*> pure f
                                                <*> mapM normalize es
  normalize (TLet        ds e) = TLet <$> mapM normalizeBinding ds
                                      <*> normalize e
    where normalizeBinding (v, b) = (,) <$> normalize v <*> normalize b
  normalize (TOr          a b) = TOr <$> normalize a
                                     <*> normalize b
  normalize (TCase    ct e bs) = TCase ct <$> normalize e
                                          <*> mapM normalize bs
  normalize (TFree       vs e) = TFree <$> mapM normalize vs
                                       <*> normalize e
  normalize (TTyped     e ty') = TTyped <$> normalize e
                                        <*> normalize ty'

instance Normalize TBranchExpr where
  normalize (TBranch p e) = TBranch <$> normalize p <*> normalize e

instance Normalize TPattern where
  normalize (TPattern  ty c vs) = TPattern <$> normalize ty
                                           <*> pure c
                                           <*> mapM normalize vs
  normalize (TLPattern ty    l) = flip TLPattern l <$> normalize ty

-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

trQualIdent :: QualIdent -> FlatState QName
trQualIdent qid = do
  mid <- getModuleIdent
  return $ (moduleName $ fromMaybe mid mid', idName i)
  where
  mid' | i `elem` [listId, consId, nilId, unitId] || isTupleId i
       = Just preludeMIdent
       | otherwise
       = qidModule qid
  i = qidIdent qid

getTypeVisibility :: QualIdent -> FlatState Visibility
getTypeVisibility i = S.gets $ \s ->
  if Set.member (unqualify i) (tyExports s) then Public else Private

getVisibility :: QualIdent -> FlatState Visibility
getVisibility i = S.gets $ \s ->
  if Set.member (unqualify i) (valExports s) then Public else Private
