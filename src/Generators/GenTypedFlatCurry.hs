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
import           Curry.FlatCurry.Annotated.Goodies (typeName)
import           Curry.FlatCurry.Annotated.Type
import           Curry.FlatCurry.Annotated.Typing
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

import qualified IL as IL
import Transformations     (transType)

-- transforms intermediate language code (IL) to typed FlatCurry code
genTypedFlatCurry :: CompilerEnv -> CS.Module Type -> IL.Module
                  -> AProg TypeExpr
genTypedFlatCurry env mdl il = patchPrelude $ run env mdl (trModule il)

-- -----------------------------------------------------------------------------
-- Addition of primitive types for lists and tuples to the Prelude
-- -----------------------------------------------------------------------------

patchPrelude :: AProg a -> AProg a
patchPrelude p@(AProg n _ ts fs os)
  | n == prelude = AProg n [] ts' fs os
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

trModule :: IL.Module -> FlatState (AProg TypeExpr)
trModule (IL.Module mid is ds) = do
  is' <- getImports is
  sns <- getTypeSynonyms >>= concatMapM trTypeSynonym
  tds <- concatMapM trTypeDecl ds
  fds <- concatMapM (return . map runNormalization <=< trAFuncDecl) ds
  ops <- getFixities >>= concatMapM trIOpDecl
  return $ AProg (moduleName mid) is' (sns ++ tds) fds ops

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
trAFuncDecl :: IL.Decl -> FlatState [AFuncDecl TypeExpr]
trAFuncDecl (IL.FunctionDecl f vs _ e) = do
  f'  <- trQualIdent f
  a   <- getArity f
  vis <- getVisibility f
  ty' <- trType ty
  r'  <- trARule ty vs e
  return [AFunc f' a vis ty' r']
  where ty = foldr IL.TypeArrow (IL.typeOf e) $ map fst vs
trAFuncDecl (IL.ExternalDecl     f ty) = do
  f'   <- trQualIdent f
  a    <- getArity f
  vis  <- getVisibility f
  ty'  <- trType ty
  r'   <- trAExternal ty f
  return [AFunc f' a vis ty' r']
trAFuncDecl _                           = return []

-- Translate a function rule.
-- Resets variable index so that for every rule variables start with index 1
trARule :: IL.Type -> [(IL.Type, Ident)] -> IL.Expression
        -> FlatState (ARule TypeExpr)
trARule ty vs e = withFreshEnv $ ARule <$> trType ty
                                    <*> mapM (uncurry newVar) vs
                                    <*> trAExpr e

trAExternal :: IL.Type -> QualIdent -> FlatState (ARule TypeExpr)
trAExternal ty f = flip AExternal (qualName f) <$> trType ty

-- Translate an expression
trAExpr :: IL.Expression -> FlatState (AExpr TypeExpr)
trAExpr (IL.Literal       ty l) = ALit <$> trType ty <*> trLiteral l
trAExpr (IL.Variable      ty v) = AVar <$> trType ty <*> getVarIndex v
trAExpr (IL.Function    ty f _) = genCall Fun ty f []
trAExpr (IL.Constructor ty c _) = genCall Con ty c []
trAExpr (IL.Apply        e1 e2) = trApply e1 e2
trAExpr c@(IL.Case      t e bs) = flip ACase (cvEval t) <$> trType (IL.typeOf c) <*> trAExpr e
                                  <*> mapM (inNestedEnv . trAlt) bs
trAExpr (IL.Or           e1 e2) = AOr <$> trType (IL.typeOf e1) <*> trAExpr e1 <*> trAExpr e2
trAExpr (IL.Exist          v e) = inNestedEnv $ do
  v' <- newVar (IL.typeOf e) v
  e' <- trAExpr e
  ty' <- trType (IL.typeOf e)
  return $ case e' of AFree ty'' vs e'' -> AFree ty'' (v' : vs) e''
                      _                 -> AFree ty'  (v' : []) e'
trAExpr (IL.Let (IL.Binding v b) e) = inNestedEnv $ do
  v' <- newVar (IL.typeOf b) v
  b' <- trAExpr b
  e' <- trAExpr e
  ty' <- trType $ IL.typeOf e
  return $ case e' of ALet ty'' bs e'' -> ALet ty'' ((v', b'):bs) e''
                      _                -> ALet ty'  ((v', b'):[]) e'
trAExpr (IL.Letrec   bs e) = inNestedEnv $ do
  let (vs, es) = unzip [ ((IL.typeOf b, v), b) | IL.Binding v b <- bs]
  ALet <$> trType (IL.typeOf e)
       <*> (zip <$> mapM (uncurry newVar) vs <*> mapM trAExpr es)
       <*> trAExpr e
trAExpr (IL.Typed e _) = ATyped <$> ty' <*> trAExpr e <*> ty'
  where ty' = trType $ IL.typeOf e

-- Translate a literal
trLiteral :: IL.Literal -> FlatState Literal
trLiteral (IL.Char  c) = return $ Charc  c
trLiteral (IL.Int   i) = return $ Intc   i
trLiteral (IL.Float f) = return $ Floatc f

-- Translate a higher-order application
trApply :: IL.Expression -> IL.Expression -> FlatState (AExpr TypeExpr)
trApply e1 e2 = genFlatApplic e1 [e2]
  where
  genFlatApplic e es = case e of
    IL.Apply        ea eb -> genFlatApplic ea (eb:es)
    IL.Function    ty f _ -> genCall Fun ty f es
    IL.Constructor ty c _ -> genCall Con ty c es
    _ -> do
      expr <- trAExpr e
      genApply expr es

-- Translate an alternative
trAlt :: IL.Alt -> FlatState (ABranchExpr TypeExpr)
trAlt (IL.Alt p e) = ABranch <$> trPat p <*> trAExpr e

-- Translate a pattern
trPat :: IL.ConstrTerm -> FlatState (APattern TypeExpr)
trPat (IL.LiteralPattern        ty l) = ALPattern <$> trType ty <*> trLiteral l
trPat (IL.ConstructorPattern ty c vs) = do
  qty <- trType $ foldr IL.TypeArrow ty $ map fst vs
  APattern  <$> trType ty <*> ((\q -> (q, qty)) <$> trQualIdent c) <*> mapM (uncurry newVar) vs
trPat (IL.VariablePattern        _ _) = internalError "GenTypedFlatCurry.trPat"

-- Convert a case type
cvEval :: IL.Eval -> CaseType
cvEval IL.Rigid = Rigid
cvEval IL.Flex  = Flex

data Call = Fun | Con

-- Generate a function or constructor call
genCall :: Call -> IL.Type -> QualIdent -> [IL.Expression]
        -> FlatState (AExpr TypeExpr)
genCall call ty f es = do
  f'    <- trQualIdent f
  arity <- getArity f
  case compare supplied arity of
    LT -> genAComb ty f' es (part call (arity - supplied))
    EQ -> genAComb ty f' es (full call)
    GT -> do
      let (es1, es2) = splitAt arity es
      funccall <- genAComb ty f' es1 (full call)
      genApply funccall es2
  where
  supplied = length es
  full Fun = FuncCall
  full Con = ConsCall
  part Fun = FuncPartCall
  part Con = ConsPartCall

genAComb :: IL.Type -> QName -> [IL.Expression] -> CombType -> FlatState (AExpr TypeExpr)
genAComb ty qid es ct = do
  ty' <- trType ty
  let ty'' = defunc ty' (length es)
  AComb ty'' ct (qid, ty') <$> mapM trAExpr es
  where
  defunc t               0 = t
  defunc (FuncType _ t2) n = defunc t2 (n - 1)
  defunc _               _ = internalError "GenTypedFlatCurry.genAComb.defunc"

genApply :: AExpr TypeExpr -> [IL.Expression] -> FlatState (AExpr TypeExpr)
genApply e es = do
  ap  <- trQualIdent $ qApplyId
  es' <- mapM trAExpr es
  return $ foldl (\e1 e2 -> let FuncType ty1 ty2 = typeOf e1 in AComb ty2 FuncCall (ap, FuncType (FuncType ty1 ty2) (FuncType ty1 ty2)) [e1, e2]) e es'

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
  normalize (x, y) = ((,) x) <$> normalize y

instance Normalize a => Normalize (AFuncDecl a) where
  normalize (AFunc f a v ty r) = AFunc f a v <$> normalize ty <*> normalize r

instance Normalize a => Normalize (ARule a) where
  normalize (ARule     ty vs e) = ARule <$> normalize ty
                                        <*> mapM normalize vs
                                        <*> normalize e
  normalize (AExternal ty    s) = flip AExternal s <$> normalize ty

instance Normalize a => Normalize (AExpr a) where
  normalize (AVar  ty       v) = flip AVar  v  <$> normalize ty
  normalize (ALit  ty       l) = flip ALit  l  <$> normalize ty
  normalize (AComb ty ct f es) = flip AComb ct <$> normalize ty
                                               <*> normalize f
                                               <*> mapM normalize es
  normalize (ALet  ty    ds e) = ALet <$> normalize ty
                                      <*> mapM normalizeBinding ds
                                      <*> normalize e
    where normalizeBinding (v, b) = (,) <$> normalize v <*> normalize b
  normalize (AOr   ty     a b) = AOr <$> normalize ty <*> normalize a
                                     <*> normalize b
  normalize (ACase ty ct e bs) = flip ACase ct <$> normalize ty <*> normalize e
                                               <*> mapM normalize bs
  normalize (AFree  ty   vs e) = AFree <$> normalize ty <*> mapM normalize vs
                                       <*> normalize e
  normalize (ATyped ty  e ty') = ATyped <$> normalize ty <*> normalize e
                                        <*> normalize ty'

instance Normalize a => Normalize (ABranchExpr a) where
  normalize (ABranch p e) = ABranch <$> normalize p <*> normalize e

instance Normalize a => Normalize (APattern a) where
  normalize (APattern  ty c vs) = APattern <$> normalize ty <*> normalize c
                                           <*> mapM normalize vs
  normalize (ALPattern ty    l) = flip ALPattern l <$> normalize ty

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
