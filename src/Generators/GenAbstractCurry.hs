{- |
    Module      :  $Header$
    Description :  Generation of AbstractCurry program terms
    Copyright   :  (c) 2005        Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of an 'AbstractCurry' program term
    for a given 'Curry' module.
-}
{-# LANGUAGE CPP #-}
module Generators.GenAbstractCurry (genAbstractCurry) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative          ((<$>), (<*>), pure)
#endif
import           Control.Monad.Extra
import qualified Control.Monad.State as S     (State, evalState, get, gets
                                              , modify, put, when)
import qualified Data.Map            as Map   (Map, empty, fromList, lookup
                                              , union)
import qualified Data.Maybe          as Maybe (fromJust, fromMaybe, listToMaybe)
import qualified Data.Set            as Set   (Set, empty, insert, member)
import qualified Data.Traversable    as T     (forM)

import Curry.AbstractCurry
import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax

import Base.CurryTypes (fromPredType, toType, toPredType)
import Base.Expr       (bv)
import Base.Messages   (internalError)
import Base.NestEnv
import Base.Types      (arrowArity, PredType, unpredType, TypeScheme (..))
import Base.TypeSubst

import Env.Value       (ValueEnv, ValueInfo (..), qualLookupValue)
import Env.OpPrec      (mkPrec)

import CompilerEnv

type GAC a = S.State AbstractEnv a

-- ---------------------------------------------------------------------------
-- Interface
-- ---------------------------------------------------------------------------

-- |Generate an AbstractCurry program term from the syntax tree
--  when uacy flag is set untype AbstractCurry is generated
genAbstractCurry :: Bool -> CompilerEnv -> Module PredType -> CurryProg
genAbstractCurry uacy env mdl
  = S.evalState (trModule mdl) (abstractEnv uacy env mdl)

-- ---------------------------------------------------------------------------
-- Conversion from Curry to AbstractCurry
-- ---------------------------------------------------------------------------

trModule :: Module PredType -> GAC CurryProg
trModule (Module _ _ _ mid _ is ds) =
  CurryProg mid' is' <$> dflt' <*> cds' <*> ids' <*> ts' <*> fs' <*> os'
  where
  mid'  = moduleName mid
  is'   = map cvImportDecl is
  dflt' = Maybe.listToMaybe <$> concatMapM (withLocalEnv . trDefaultDecl) ds
  cds'  = concatMapM (withLocalEnv . trClassDecl) ds
  ids'  = concatMapM (withLocalEnv . trInstanceDecl) ds
  ts'   = concatMapM (withLocalEnv . trTypeDecl) ds
  fs'   = concatMapM (withLocalEnv . trFuncDecl True) ds
  os'   = concatMapM (withLocalEnv . trInfixDecl) ds

cvImportDecl :: ImportDecl -> String
cvImportDecl (ImportDecl _ mid _ _ _) = moduleName mid

trDefaultDecl :: Decl a -> GAC [CDefaultDecl]
trDefaultDecl (DefaultDecl _ tys) = (\tys' -> [CDefaultDecl tys'])
  <$> mapM trTypeExpr tys
trDefaultDecl _                   = return []

trClassDecl :: Decl PredType -> GAC [CClassDecl]
trClassDecl (ClassDecl _ _ cx cls tv ds) =
  (\cls' v' cx' tv' ds' -> [CClass cls' v' cx' tv' ds'])
    <$> trGlobalIdent cls <*> getTypeVisibility cls <*> trContext cx
    <*> getTVarIndex tv <*> concatMapM (trClassMethodDecl sigs fs) ds
  where fs = [f | FunctionDecl _ _ f _ <- ds]
        sigs = signatures ds
trClassDecl _ = return []

-- We ignore type signatures for class methods with a given default
-- implementation as declarations for those are generated anyway.
-- For function declarations we use the equation's arity instead of
-- the one from the value environment or 0.
trClassMethodDecl :: [(Ident, QualTypeExpr)] -> [Ident] -> Decl PredType
                  -> GAC [CFuncDecl]
trClassMethodDecl sigs fs (TypeSig p [f] _) | f `notElem` fs =
  trClassMethodDecl sigs fs $ FunctionDecl p undefined f []
trClassMethodDecl sigs fs (TypeSig p (f:f':fs') qty) =
  liftM2 (++) (trClassMethodDecl sigs fs $ TypeSig p [f] qty)
              (trClassMethodDecl sigs fs $ TypeSig p (f':fs') qty)
trClassMethodDecl sigs _ (FunctionDecl _ _ f eqs) =
  (\f' a v ty rs -> [CFunc f' a v ty rs]) <$> trGlobalIdent f
  <*> pure (maybe 0 eqnArity $ Maybe.listToMaybe eqs)
  <*> getVisibility (unRenameIdent f)
  <*> trQualTypeExpr (Maybe.fromJust $ lookup f sigs) <*> mapM trEquation eqs
trClassMethodDecl _ _ _ = return []

trInstanceDecl :: Decl PredType -> GAC [CInstanceDecl]
trInstanceDecl (InstanceDecl _ _ cx qcls ty ds) =
  (\qcls' cx' ty' ds' -> [CInstance qcls' cx' ty' ds']) <$> trQual qcls
  <*> trContext cx <*> trTypeExpr ty <*> mapM (trInstanceMethodDecl qcls ty) ds
trInstanceDecl _ = return []

-- Again, we use the equation's arity for function declarations instead of
-- the one from the value.
trInstanceMethodDecl :: QualIdent -> TypeExpr -> Decl PredType -> GAC CFuncDecl
trInstanceMethodDecl qcls ty (FunctionDecl _ _ f eqs) = do
  uacy <- S.gets untypedAcy
  qty <- if uacy
           then return $ QualTypeExpr NoSpanInfo [] $
                           ConstructorType NoSpanInfo prelUntyped
           else getQualType' (qualifyLike qcls $ unRenameIdent f)
  CFunc <$> trLocalIdent f <*> pure (eqnArity $ head eqs) <*> pure Public
        <*> trInstanceMethodType ty qty <*> mapM trEquation eqs
trInstanceMethodDecl _ _ _ = internalError "GenAbstractCurry.trInstanceMethodDecl"

-- Transforms a class method type into an instance method's type by replacing
-- the class variable with the given instance type. The implicit class context
-- is dropped in doing so.
trInstanceMethodType :: TypeExpr -> QualTypeExpr -> GAC CQualTypeExpr
trInstanceMethodType ity (QualTypeExpr _ cx ty) =
  trQualTypeExpr $ fromPredType identSupply $
    subst (bindSubst 0 (toType [] ity) idSubst) $
      toPredType (take 1 identSupply) $ QualTypeExpr NoSpanInfo (drop 1 cx) ty

trTypeDecl :: Decl a -> GAC [CTypeDecl]
trTypeDecl (DataDecl    _ t vs cs clss) =
  (\t' v vs' cs' clss' -> [CType t' v vs' cs' clss'])
  <$> trGlobalIdent t <*> getTypeVisibility t
  <*> mapM genTVarIndex vs <*> mapM trConsDecl cs
  <*> mapM trQual clss
trTypeDecl (TypeDecl    _ t vs ty) = (\t' v vs' ty' -> [CTypeSyn t' v vs' ty'])
  <$> trGlobalIdent t <*> getTypeVisibility t
  <*> mapM genTVarIndex vs <*> trTypeExpr ty
trTypeDecl (NewtypeDecl _ t vs nc clss) =
  (\t' v vs' nc' clss' -> [CNewType t' v vs' nc' clss'])
  <$> trGlobalIdent t <*> getTypeVisibility t
  <*> mapM genTVarIndex vs <*> trNewConsDecl nc
  <*> mapM trQual clss
trTypeDecl (ExternalDataDecl _ t vs) =
  (\t' v vs' -> [CType t' v vs' [] []])
  <$> trGlobalIdent t <*> getTypeVisibility t <*> mapM genTVarIndex vs
trTypeDecl _                       = return []

trConsDecl :: ConstrDecl -> GAC CConsDecl
trConsDecl (ConstrDecl  _ c tys) = inNestedTScope $ CCons
  <$> trGlobalIdent c <*> getVisibility c <*> mapM trTypeExpr tys
trConsDecl (ConOpDecl p ty1 op ty2) = inNestedTScope $ trConsDecl $
  ConstrDecl p op [ty1, ty2]
trConsDecl (RecordDecl   _ c fs) = inNestedTScope $ CRecord
  <$> trGlobalIdent c <*> getVisibility c <*> concatMapM trFieldDecl fs

trFieldDecl :: FieldDecl -> GAC [CFieldDecl]
trFieldDecl (FieldDecl _ ls ty) = T.forM ls $ \l ->
  CField <$> trGlobalIdent l <*> getVisibility l <*> trTypeExpr ty

trNewConsDecl :: NewConstrDecl -> GAC CConsDecl
trNewConsDecl (NewConstrDecl _ nc      ty) = CCons
  <$> trGlobalIdent nc <*> getVisibility nc <*> ((:[]) <$> trTypeExpr ty)
trNewConsDecl (NewRecordDecl p nc (l, ty)) = CRecord
  <$> trGlobalIdent nc <*> getVisibility nc <*> trFieldDecl (FieldDecl p [l] ty)

trTypeExpr :: TypeExpr -> GAC CTypeExpr
trTypeExpr (ConstructorType _ q) = CTCons <$> trQual q
trTypeExpr (ApplyType _ ty1 ty2) = CTApply <$> trTypeExpr ty1 <*> trTypeExpr ty2
trTypeExpr (VariableType    _ v) = CTVar  <$> getTVarIndex v
trTypeExpr (TupleType     _ tys) =
  trTypeExpr $ foldl (ApplyType NoSpanInfo)
                     (ConstructorType NoSpanInfo $ qTupleId $ length tys) tys
trTypeExpr (ListType       _ ty) =
  trTypeExpr $ ApplyType NoSpanInfo (ConstructorType NoSpanInfo qListId) ty
trTypeExpr (ArrowType _ ty1 ty2) = CFuncType <$> trTypeExpr ty1 <*> trTypeExpr ty2
trTypeExpr (ParenType      _ ty) = trTypeExpr ty
trTypeExpr (ForallType    _ _ _) = internalError "GenAbstractCurry.trTypeExpr"

trConstraint :: Constraint -> GAC CConstraint
trConstraint (Constraint _ q ty) = (,) <$> trQual q <*> trTypeExpr ty

trContext :: Context -> GAC CContext
trContext cx = CContext <$> mapM trConstraint cx

trQualTypeExpr :: QualTypeExpr -> GAC CQualTypeExpr
trQualTypeExpr (QualTypeExpr _ cx ty) =
  CQualType <$> trContext cx <*> trTypeExpr ty

trInfixDecl :: Decl a -> GAC [COpDecl]
trInfixDecl (InfixDecl _ fix mprec ops) = mapM trInfix (reverse ops)
  where
  trInfix op = COp <$> trGlobalIdent op <*> return (cvFixity fix)
                   <*> return (fromInteger (mkPrec mprec))
  cvFixity InfixL = CInfixlOp
  cvFixity InfixR = CInfixrOp
  cvFixity Infix  = CInfixOp
trInfixDecl _ = return []

trFuncDecl :: Bool -> Decl PredType -> GAC [CFuncDecl]
trFuncDecl global (FunctionDecl  _ pty f eqs)
  =   (\f' a v ty rs -> [CFunc f' a v ty rs])
  <$> trFuncName global f <*> pure (eqnArity $ head eqs) <*> getVisibility f
  <*> getQualType f pty <*> mapM trEquation eqs
trFuncDecl global (ExternalDecl         _ vs)
  =   T.forM vs $ \(Var pty f) -> CFunc
  <$> trFuncName global f <*> pure (arrowArity $ unpredType pty)
  <*> getVisibility f <*> getQualType f pty <*> return []
trFuncDecl _      _                           = return []

trFuncName :: Bool -> Ident -> GAC QName
trFuncName global = if global then trGlobalIdent else trLocalIdent

trEquation :: Equation PredType -> GAC CRule
trEquation (Equation _ lhs rhs) = inNestedScope
                                $ CRule <$> trLhs lhs <*> trRhs rhs

trLhs :: Lhs a -> GAC [CPattern]
trLhs = mapM trPat . snd . flatLhs

trRhs :: Rhs PredType -> GAC CRhs
trRhs (SimpleRhs _ _ e ds) = inNestedScope $ do
  mapM_ insertDeclLhs ds
  CSimpleRhs <$> trExpr e <*> concatMapM trLocalDecl ds
trRhs (GuardedRhs _ _ gs ds) = inNestedScope $ do
  mapM_ insertDeclLhs ds
  CGuardedRhs <$> mapM trCondExpr gs <*> concatMapM trLocalDecl ds

trCondExpr :: CondExpr PredType -> GAC (CExpr, CExpr)
trCondExpr (CondExpr _ g e) = (,) <$> trExpr g <*> trExpr e

trLocalDecls :: [Decl PredType] -> GAC [CLocalDecl]
trLocalDecls ds = do
  mapM_ insertDeclLhs ds
  concatMapM trLocalDecl ds

-- Insert all variables declared in local declarations
insertDeclLhs :: Decl a -> GAC ()
insertDeclLhs   (PatternDecl      _ p _) = mapM_ genVarIndex (bv p)
insertDeclLhs   (FreeDecl          _ vs) = mapM_ genVarIndex (map varIdent vs)
insertDeclLhs s@(TypeSig          _ _ _) = do
  uacy <- S.gets untypedAcy
  S.when uacy (insertSig s)
insertDeclLhs _                          = return ()

trLocalDecl :: Decl PredType -> GAC [CLocalDecl]
trLocalDecl f@(FunctionDecl    _ _ _ _) = map CLocalFunc <$> trFuncDecl False f
trLocalDecl f@(ExternalDecl        _ _) = map CLocalFunc <$> trFuncDecl False f
trLocalDecl (PatternDecl       _ p rhs) = (\p' rhs' -> [CLocalPat p' rhs'])
                                          <$> trPat p <*> trRhs rhs
trLocalDecl (FreeDecl             _ vs) = (\vs' -> [CLocalVars vs'])
                                          <$> mapM getVarIndex (map varIdent vs)
trLocalDecl _                           = return [] -- can not occur (types etc.)

insertSig :: Decl a -> GAC ()
insertSig (TypeSig _ fs qty) = do
  sigs <- S.gets typeSigs
  let lsigs = Map.fromList [(f, qty) | f <- fs]
  S.modify $ \env -> env { typeSigs = sigs `Map.union` lsigs }
insertSig _                 = return ()

trExpr :: Expression PredType -> GAC CExpr
trExpr (Literal       _ _ l) = return (CLit $ cvLiteral l)
trExpr (Variable      _ _ v)
  | isQualified v = CSymbol <$> trQual v
  | otherwise     = lookupVarIndex (unqualify v) >>= \mvi -> case mvi of
    Just vi -> return (CVar vi)
    _       -> CSymbol <$> trQual v
trExpr (Constructor   _ _ c) = CSymbol <$> trQual c
trExpr (Paren           _ e) = trExpr e
trExpr (Typed       _ e qty) = CTyped <$> trExpr e <*> trQualTypeExpr qty
trExpr (Record     _ _ c fs) = CRecConstr <$> trQual c
                                          <*> mapM (trField trExpr) fs
trExpr (RecordUpdate _ e fs) = CRecUpdate <$> trExpr e
                                          <*> mapM (trField trExpr) fs
trExpr (Tuple          _ es) =
  trExpr $ apply (Variable NoSpanInfo undefined $ qTupleId $ length es) es
trExpr (List         _ _ es) =
  trExpr $ foldr (Apply NoSpanInfo . Apply NoSpanInfo
                   (Constructor NoSpanInfo undefined qConsId))
                 (Constructor NoSpanInfo undefined qNilId)
                 es
trExpr (ListCompr    _ e ds) = inNestedScope $ flip CListComp
                               <$> mapM trStatement ds <*> trExpr e
trExpr (EnumFrom              _ e) =
  trExpr $ apply (Variable NoSpanInfo undefined qEnumFromId) [e]
trExpr (EnumFromThen      _ e1 e2) =
  trExpr $ apply (Variable NoSpanInfo undefined qEnumFromThenId) [e1, e2]
trExpr (EnumFromTo        _ e1 e2) =
  trExpr $ apply (Variable NoSpanInfo undefined qEnumFromToId) [e1, e2]
trExpr (EnumFromThenTo _ e1 e2 e3) =
  trExpr $ apply (Variable NoSpanInfo undefined qEnumFromThenToId) [e1, e2, e3]
trExpr (UnaryMinus            _ e) =
  trExpr $ apply (Variable NoSpanInfo undefined qNegateId) [e]
trExpr (Apply             _ e1 e2) = CApply <$> trExpr e1 <*> trExpr e2
trExpr (InfixApply     _ e1 op e2) = trExpr $ apply (infixOp op) [e1, e2]
trExpr (LeftSection        _ e op) = trExpr $ apply (infixOp op) [e]
trExpr (RightSection       _ op e) =
  trExpr $ apply (Variable NoSpanInfo undefined qFlip) [infixOp op, e]
trExpr (Lambda             _ ps e) = inNestedScope $
                                     CLambda <$> mapM trPat ps <*> trExpr e
trExpr (Let              _ _ ds e) = inNestedScope $
                                     CLetDecl <$> trLocalDecls ds <*> trExpr e
trExpr (Do               _ _ ss e) = inNestedScope $
                                     (\ss' e' -> CDoExpr (ss' ++ [CSExpr e']))
                                     <$> mapM trStatement ss <*> trExpr e
trExpr (IfThenElse     _ e1 e2 e3) =
  trExpr $ apply (Variable NoSpanInfo undefined qIfThenElseId) [e1, e2, e3]
trExpr (Case          _ _ ct e bs) = CCase (cvCaseType ct)
                                     <$> trExpr e <*> mapM trAlt bs

cvCaseType :: CaseType -> CCaseType
cvCaseType Flex  = CFlex
cvCaseType Rigid = CRigid

trStatement :: Statement PredType -> GAC CStatement
trStatement (StmtExpr _   e)  = CSExpr     <$> trExpr e
trStatement (StmtDecl _ _ ds) = CSLet      <$> trLocalDecls ds
trStatement (StmtBind _ p e)  = flip CSPat <$> trExpr e <*> trPat p

trAlt :: Alt PredType -> GAC (CPattern, CRhs)
trAlt (Alt _ p rhs) = inNestedScope $ (,) <$> trPat p <*> trRhs rhs

trPat :: Pattern a -> GAC CPattern
trPat (LiteralPattern         _ _ l) = return (CPLit $ cvLiteral l)
trPat (VariablePattern        _ _ v) = CPVar <$> getVarIndex v
trPat (ConstructorPattern  _ _ c ps) = CPComb <$> trQual c <*> mapM trPat ps
trPat (InfixPattern    _ a p1 op p2) =
  trPat $ ConstructorPattern NoSpanInfo a op [p1, p2]
trPat (ParenPattern             _ p) = trPat p
trPat (RecordPattern       _ _ c fs) = CPRecord <$> trQual c
                                              <*> mapM (trField trPat) fs
trPat (TuplePattern            _ ps) =
  trPat $ ConstructorPattern NoSpanInfo undefined (qTupleId $ length ps) ps
trPat (ListPattern           _ _ ps) = trPat $
  foldr (\x1 x2 -> ConstructorPattern NoSpanInfo undefined qConsId [x1, x2])
        (ConstructorPattern NoSpanInfo undefined qNilId [])
        ps
trPat (NegativePattern        _ a l) =
  trPat $ LiteralPattern NoSpanInfo a $ negateLiteral l
trPat (AsPattern              _ v p) = CPAs <$> getVarIndex v<*> trPat p
trPat (LazyPattern              _ p) = CPLazy <$> trPat p
trPat (FunctionPattern     _ _ f ps) = CPFuncComb <$> trQual f <*> mapM trPat ps
trPat (InfixFuncPattern _ a p1 f p2) =
  trPat (FunctionPattern NoSpanInfo a f [p1, p2])

trField :: (a -> GAC b) -> Field a -> GAC (CField b)
trField act (Field _ l x) = (,) <$> trQual l <*> act x

negateLiteral :: Literal -> Literal
negateLiteral (Int    i) = Int   (-i)
negateLiteral (Float  f) = Float (-f)
negateLiteral _          = internalError "GenAbstractCurry.negateLiteral"

cvLiteral :: Literal -> CLiteral
cvLiteral (Char   c) = CCharc   c
cvLiteral (Int    i) = CIntc    i
cvLiteral (Float  f) = CFloatc  f
cvLiteral (String s) = CStringc s

trQual :: QualIdent -> GAC QName
trQual qid
  | n `elem` [unitId, listId, nilId, consId] = return ("Prelude", idName n)
  | isTupleId n                              = return ("Prelude", idName n)
  | otherwise
  = return (maybe "" moduleName (qidModule qid), idName n)
  where n = qidIdent qid

trGlobalIdent :: Ident -> GAC QName
trGlobalIdent i = S.gets moduleId >>= \m -> return (moduleName m, idName i)

trLocalIdent :: Ident -> GAC QName
trLocalIdent i = return ("", idName i)

qFlip :: QualIdent
qFlip = qualifyWith preludeMIdent (mkIdent "flip")

qNegateId :: QualIdent
qNegateId = qualifyWith preludeMIdent (mkIdent "negate")

qIfThenElseId :: QualIdent
qIfThenElseId = qualifyWith preludeMIdent (mkIdent "ifThenElse")

prelUntyped :: QualIdent
prelUntyped = qualifyWith preludeMIdent $ mkIdent "untyped"

-------------------------------------------------------------------------------
-- This part defines an environment containing all necessary information
-- for generating the AbstractCurry representation of a CurrySyntax term.

-- |Data type for representing an AbstractCurry generator environment
data AbstractEnv = AbstractEnv
  { moduleId   :: ModuleIdent                -- ^name of the module
  , typeEnv    :: ValueEnv                   -- ^known values
  , tyExports  :: Set.Set Ident              -- ^exported type symbols
  , valExports :: Set.Set Ident              -- ^exported value symbols
  , varIndex   :: Int                        -- ^counter for variable indices
  , tvarIndex  :: Int                        -- ^counter for type variable indices
  , varEnv     :: NestEnv Int                -- ^stack of variable tables
  , tvarEnv    :: NestEnv Int                -- ^stack of type variable tables
  , untypedAcy :: Bool                       -- ^flag to indicate whether untyped
                                             --  AbstractCurry is generated
  , typeSigs   :: Map.Map Ident QualTypeExpr -- ^map of user defined type signatures
  } deriving Show

-- |Initialize the AbstractCurry generator environment
abstractEnv :: Bool -> CompilerEnv -> Module a -> AbstractEnv
abstractEnv uacy env (Module _ _ _ mid es _ ds) = AbstractEnv
  { moduleId   = mid
  , typeEnv    = valueEnv env
  , tyExports  = foldr (buildTypeExports  mid) Set.empty es'
  , valExports = foldr (buildValueExports mid) Set.empty es'
  , varIndex   = 0
  , tvarIndex  = 0
  , varEnv     = globalEnv emptyTopEnv
  , tvarEnv    = globalEnv emptyTopEnv
  , untypedAcy = uacy
  , typeSigs   = if uacy
                  then Map.fromList $ signatures ds
                  else Map.empty
  }
  where es' = case es of
          Just (Exporting _ e) -> e
          _                    -> internalError "GenAbstractCurry.abstractEnv"

-- Builds a table containing all exported identifiers from a module.
buildTypeExports :: ModuleIdent -> Export -> Set.Set Ident -> Set.Set Ident
buildTypeExports mid (ExportTypeWith _ tc _)
  | isLocalIdent mid tc = Set.insert (unqualify tc)
buildTypeExports _   _  = id

-- Builds a table containing all exported identifiers from a module.
buildValueExports :: ModuleIdent -> Export -> Set.Set Ident -> Set.Set Ident
buildValueExports mid (Export             _ q)
  | isLocalIdent mid q  = Set.insert (unqualify q)
buildValueExports mid (ExportTypeWith _ tc cs)
  | isLocalIdent mid tc = flip (foldr Set.insert) cs
buildValueExports _   _  = id

-- Looks up the unique index for the variable 'ident' in the
-- variable table of the current scope.
lookupVarIndex :: Ident -> GAC (Maybe CVarIName)
lookupVarIndex i = S.gets $ \env -> case lookupNestEnv i $ varEnv env of
  [v] -> Just (v, idName i)
  _   -> Nothing

getVarIndex :: Ident -> GAC CVarIName
getVarIndex i = S.get >>= \env -> case lookupNestEnv i $ varEnv env of
  [v] -> return (v, idName i)
  _   -> genVarIndex i

-- Generates an unique index for the  variable 'ident' and inserts it
-- into the  variable table of the current scope.
genVarIndex :: Ident -> GAC CVarIName
genVarIndex i = do
  env <- S.get
  let idx = varIndex env
  S.put $ env { varIndex = idx + 1, varEnv = bindNestEnv i idx (varEnv env) }
  return (idx, idName i)

-- Looks up the unique index for the type variable 'ident' in the type
-- variable table of the current scope.
getTVarIndex :: Ident -> GAC CTVarIName
getTVarIndex i = S.get >>= \env -> case lookupNestEnv i $ tvarEnv env of
  [v] -> return (v, idName i)
  _   -> genTVarIndex i

-- Generates an unique index for the type variable 'ident' and inserts it
-- into the type variable table of the current scope.
genTVarIndex :: Ident -> GAC CTVarIName
genTVarIndex i = do
  env <- S.get
  let idx = tvarIndex env
  S.put $ env { tvarIndex = idx + 1, tvarEnv = bindNestEnv i idx (tvarEnv env) }
  return (idx, idName i)

withLocalEnv :: GAC a -> GAC a
withLocalEnv act = do
  old <- S.get
  res <- act
  S.put old
  return res

inNestedScope :: GAC a -> GAC a
inNestedScope act = do
  (vo, to) <- S.gets $ \e -> (varEnv e, tvarEnv e)
  S.modify $ \e -> e { varEnv = nestEnv $ vo, tvarEnv = globalEnv emptyTopEnv }
  res <- act
  S.modify $ \e -> e { varEnv = vo, tvarEnv = to }
  return res

inNestedTScope :: GAC a -> GAC a
inNestedTScope act = do
  (vo, to) <- S.gets $ \e -> (varEnv e, tvarEnv e)
  S.modify $ \e -> e { varEnv = globalEnv emptyTopEnv, tvarEnv = nestEnv $ to }
  res <- act
  S.modify $ \e -> e { varEnv = vo, tvarEnv = to }
  return res

getQualType :: Ident -> PredType -> GAC CQualTypeExpr
getQualType f pty = do
  uacy <- S.gets untypedAcy
  sigs <- S.gets typeSigs
  trQualTypeExpr $ case uacy of
    True  -> Maybe.fromMaybe (QualTypeExpr NoSpanInfo [] $
                               ConstructorType NoSpanInfo prelUntyped)
                             (Map.lookup f sigs)
    False -> fromPredType identSupply pty

getQualType' :: QualIdent -> GAC QualTypeExpr
getQualType' f = do
  m     <- S.gets moduleId
  tyEnv <- S.gets typeEnv
  return $ case qualLookupValue f tyEnv of
    [Value _ _ _ (ForAll _ pty)] -> fromPredType identSupply pty
    _                          -> case qualLookupValue (qualQualify m f) tyEnv of
      [Value _ _ _ (ForAll _ pty)] -> fromPredType identSupply pty
      _                          ->
        internalError $ "GenAbstractCurry.getQualType': " ++ show f

getTypeVisibility :: Ident -> GAC CVisibility
getTypeVisibility i = S.gets $ \env ->
  if Set.member i (tyExports env) then Public else Private

getVisibility :: Ident -> GAC CVisibility
getVisibility i = S.gets $ \env ->
  if Set.member i (valExports env) then Public else Private

signatures :: [Decl a] -> [(Ident, QualTypeExpr)]
signatures ds = [(f, qty) | TypeSig _ fs qty <- ds, f <- fs]
