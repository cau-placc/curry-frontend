{- |
    Module      :  $Header$
    Description :  Lifting of lambda-expressions and local functions
    Copyright   :  (c) 2001 - 2003 Wolfgang Lux
                       2011 - 2015 Björn Peemöller
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After desugaring and simplifying the code, the compiler lifts all local
   function declarations to the top-level keeping only local variable
   declarations. The algorithm used here is similar to Johnsson's, consisting
   of two phases. First, we abstract each local function declaration,
   adding its free variables as initial parameters and update all calls
   to take these variables into account. Second, all local function
   declarations are collected and lifted to the top-level.
-}
module Curry.Frontend.Transformations.Lift (lift) where

import           Control.Arrow              (first)
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List
import qualified Data.Map            as Map (Map, empty, insert, lookup)
import           Data.Maybe                 (mapMaybe, fromJust)
import qualified Data.Set            as Set (fromList, toList, unions)

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax

import Curry.Frontend.Base.AnnotExpr
import Curry.Frontend.Base.Expr
import Curry.Frontend.Base.Messages         (internalError)
import Curry.Frontend.Base.SCC
import Curry.Frontend.Base.Types
import Curry.Frontend.Base.TypeSubst
import Curry.Frontend.Base.Typing
import Curry.Frontend.Base.Utils

import Curry.Frontend.Env.Value

lift :: ValueEnv -> Module Type -> (Module Type, ValueEnv)
lift vEnv (Module spi li ps m es is ds) = (lifted, valueEnv s')
  where
  (ds', s') = S.runState (mapM (absDecl "" []) ds) initState
  initState = LiftState m vEnv Map.empty
  lifted    = Module spi li ps m es is $ concatMap liftFunDecl ds'

-- -----------------------------------------------------------------------------
-- Abstraction
-- -----------------------------------------------------------------------------

-- Besides adding the free variables to every (local) function, the
-- abstraction pass also has to update the type environment in order to
-- reflect the new types of the abstracted functions. As usual, we use a
-- state monad transformer in order to pass the type environment
-- through. The environment constructed in the abstraction phase maps
-- each local function declaration onto its replacement expression,
-- i.e. the function applied to its free variables. In order to generate
-- correct type annotations for an inserted replacement expression, we also
-- save a function's original type. The original type is later unified with
-- the concrete type of the replaced expression to obtain a type substitution
-- which is then applied to the replacement expression.

type AbstractEnv = Map.Map Ident (Expression Type, Type)

data LiftState = LiftState
  { moduleIdent :: ModuleIdent
  , valueEnv    :: ValueEnv
  , abstractEnv :: AbstractEnv
  }

type LiftM a = S.State LiftState a

getModuleIdent :: LiftM ModuleIdent
getModuleIdent = S.gets moduleIdent

getValueEnv :: LiftM ValueEnv
getValueEnv = S.gets valueEnv

modifyValueEnv :: (ValueEnv -> ValueEnv) -> LiftM ()
modifyValueEnv f = S.modify $ \s -> s { valueEnv = f $ valueEnv s }

getAbstractEnv :: LiftM AbstractEnv
getAbstractEnv = S.gets abstractEnv

withLocalAbstractEnv :: AbstractEnv -> LiftM a -> LiftM a
withLocalAbstractEnv ae act = do
  old <- getAbstractEnv
  S.modify $ \s -> s { abstractEnv = ae }
  res <- act
  S.modify $ \s -> s { abstractEnv = old }
  return res

absDecl :: String -> [Ident] -> Decl Type -> LiftM (Decl Type)
absDecl _   lvs (FunctionDecl p ty f eqs) = FunctionDecl p ty f
                                            <$> mapM (absEquation lvs) eqs
absDecl pre lvs (PatternDecl     p t rhs) = PatternDecl p t
                                            <$> absRhs pre lvs rhs
absDecl _   _   d                         = return d

absEquation :: [Ident] -> Equation Type -> LiftM (Equation Type)
absEquation lvs (Equation p a lhs@(FunLhs _ f ts) rhs) =
  Equation p a lhs <$> absRhs (idName f ++ ".") lvs' rhs
  where lvs' = lvs ++ bv ts
absEquation _ _ = error "Lift.absEquation: no pattern match"

absRhs :: String -> [Ident] -> Rhs Type -> LiftM (Rhs Type)
absRhs pre lvs (SimpleRhs p _ e _) = simpleRhs p <$> absExpr pre lvs e
absRhs _   _   _                   = error "Lift.absRhs: no simple RHS"

-- Within a declaration group we have to split the list of declarations
-- into the function and value declarations. Only the function
-- declarations are affected by the abstraction algorithm; the value
-- declarations are left unchanged except for abstracting their right
-- hand sides.

-- The abstraction of a recursive declaration group is complicated by the
-- fact that not all functions need to call each in a recursive
-- declaration group. E.g., in the following example neither 'g' nor 'h'
-- call each other.
--
--   f = g True
--     where x = h 1
--           h z = y + z
--           y = g False
--           g z = if z then x else 0
--
-- Because of this fact, 'g' and 'h' can be abstracted separately by adding
-- only 'y' to 'h' and 'x' to 'g'. On the other hand, in the following example
--
--   f x y = g 4
--     where g p = h p + x
--           h q = k + y + q
--           k = g x
--
-- the local function 'g' uses 'h', so the free variables
-- of 'h' have to be added to 'g' as well. However, because
-- 'h' does not call 'g' it is sufficient to add only
-- 'k' and 'y' (and not 'x') to its definition. We handle this by computing
-- the dependency graph between the functions and splitting this graph into
-- its strongly connected components. Each component is then processed
-- separately, adding the free variables in the group to its functions.

-- We have to be careful with local declarations within desugared case
-- expressions. If some of the cases have guards, e.g.,
--
--   case e of
--     x | x < 1 -> 1
--     x -> let double y = y * y in double x
--
-- the desugarer at present may duplicate code. While there is no problem
-- with local variable declaration being duplicated, we must avoid to
-- lift local function declarations more than once. Therefore
-- 'absFunDecls' transforms only those function declarations
-- that have not been lifted and discards the other declarations. Note
-- that it is easy to check whether a function has been lifted by
-- checking whether an entry for its transformed name is present
-- in the value environment.

absDeclGroup :: String -> [Ident] -> [Decl Type] -> Expression Type
             -> LiftM (Expression Type)
absDeclGroup pre lvs ds e = do
  m <- getModuleIdent
  absFunDecls pre lvs' (scc bv (qfv m) fds) vds e
  where lvs' = lvs ++ bv vds
        (fds, vds) = partition isFunDecl ds

absFunDecls :: String -> [Ident] -> [[Decl Type]] -> [Decl Type]
            -> Expression Type -> LiftM (Expression Type)
absFunDecls pre lvs []         vds e = do
  vds' <- mapM (absDecl pre lvs) vds
  e' <- absExpr pre lvs e
  return (mkLet vds' e')
absFunDecls pre lvs (fds:fdss) vds e = do
  m <- getModuleIdent
  env <- getAbstractEnv
  vEnv <- getValueEnv
  let -- defined functions
      fs      = bv fds
      -- function types
      ftys    = map extractFty fds
      extractFty (FunctionDecl _ _ f (Equation _ _ (FunLhs _ _ ts) rhs : _)) =
        (f, foldr (TypeArrow . typeOf) (typeOf rhs) ts)
      extractFty _                                                         =
        internalError "Lift.absFunDecls.extractFty"
      -- typed free variables on the right-hand sides
      fvsRhs  = Set.unions
                  [ Set.fromList (filter (not . isDummyType . fst)
                                         (maybe [(ty, v)]
                                                (qafv' ty)
                                                (Map.lookup v env)))
                  | (ty, v) <- concatMap (qafv m) fds ]
      -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
      -- !!! HACK: When calculating the typed free variables on the     !!!
      -- !!! right-hand side, we have to filter out the ones annotated  !!!
      -- !!! with dummy types (see below). Additionally, we have to be  !!!
      -- !!! careful when we calculate the typed free variables in a    !!!
      -- !!! replacement expression: We have to unify the original      !!!
      -- !!! function type with the instantiated function type in order !!!
      -- !!! to obtain a type substitution that can then be applied to  !!!
      -- !!! the typed free variables in the replacement expression.    !!!
      -- !!! This is analogous to the procedure when inserting a        !!!
      -- !!! replacement expression with a correct type annotation      !!!
      -- !!! (see 'absType' in 'absExpr' below).                        !!!
      -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
      qafv' ty (re, fty) =
        let unifier = matchType fty ty idSubst
        in  map (\(ty', v) -> (subst unifier ty', v)) $ qafv m re
      -- free variables that are local
      fvs     = filter ((`elem` lvs) . snd) (Set.toList fvsRhs)
      -- extended abstraction environment
      env'    = foldr bindF env fs
      -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
      -- !!! HACK: Since we do not know how to annotate the function    !!!
      -- !!! call within the replacement expression until the replace-  !!!                          !!!
      -- !!! ment expression is actually inserted (see 'absType' in     !!!
      -- !!! 'absExpr' below), we use a dummy type for this. In turn,   !!!
      -- !!! this dummy type has to be filtered out when calculating    !!!
      -- !!! the typed free variables on right-hand sides (see above).  !!!                                             !!!
      -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
      bindF f =
        Map.insert f ( apply (mkFun m pre dummyType f) (map (uncurry mkVar) fvs)
                     , fromJust $ lookup f ftys )
      -- newly abstracted functions
      fs'     = filter (\f -> null $ lookupValue (liftIdent pre f) vEnv) fs
  withLocalAbstractEnv env' $ do
    -- add variables to functions
    fds' <- mapM (absFunDecl pre fvs lvs) [d | d <- fds, any (`elem` fs') (bv d)]
    -- abstract remaining declarations
    e'   <- absFunDecls pre lvs fdss vds e
    return (mkLet fds' e')

-- When the free variables of a function are abstracted, the type of the
-- function must be changed as well.

absFunDecl :: String -> [(Type, Ident)] -> [Ident] -> Decl Type
           -> LiftM (Decl Type)
absFunDecl pre fvs lvs (FunctionDecl p ty f eqs) = do
  m <- getModuleIdent
  d <- absDecl pre lvs $ FunctionDecl p ty f' eqs'
  case d of
    FunctionDecl _ _ _ eqs'' -> do
      modifyValueEnv $ bindGlobalInfo
        (\qf tySc -> Value qf Nothing (eqnArity $ head eqs') tySc) m f' $
                    polyType ty''
      return $ FunctionDecl p ty'' f' eqs''
    _ -> internalError "Lift.absFunDecl: not a function declaration"
  where f' = liftIdent pre f
        ty' = case eqs' of
                Equation _ _ (FunLhs _ _ ts') rhs' : _
                  -> foldr (TypeArrow . typeOf) (typeOf rhs') ts'
                _ -> internalError "Lift.absFunDecl: Malformed equation"
        ty'' = genType ty'
        eqs' = map addVars eqs
        genType ty''' = subst (foldr2 bindSubst idSubst tvs tvs') ty'''
          where tvs = nub (typeVars ty''')
                tvs' = map TypeVariable [0 ..]
        addVars (Equation p' a (FunLhs _ _ ts) rhs) =
          Equation p' a (FunLhs NoSpanInfo
            f' (map (uncurry (VariablePattern NoSpanInfo)) fvs ++ ts)) rhs
        addVars _ = error "Lift.absFunDecl.addVars: no pattern match"
absFunDecl pre _ _ (ExternalDecl p vs) = ExternalDecl p <$> mapM (absVar pre) vs
absFunDecl _ _ _ _ = error "Lift.absFunDecl: no pattern match"

absVar :: String -> Var Type -> LiftM (Var Type)
absVar pre (Var ty f) = do
  m <- getModuleIdent
  modifyValueEnv $ bindGlobalInfo
    (\qf tySc -> Value qf Nothing (arrowArity ty) tySc) m f' $ polyType ty
  return $ Var ty f'
  where f' = liftIdent pre f

absExpr :: String -> [Ident] -> Expression Type -> LiftM (Expression Type)
absExpr _   _   l@(Literal     _ _ _) = return l
absExpr pre lvs var@(Variable _ ty v)
  | isQualified v = return var
  | otherwise     = do
    getAbstractEnv >>= \env -> case Map.lookup (unqualify v) env of
      Nothing       -> return var
      Just (e, fty) -> let unifier = matchType fty ty idSubst
                       in  absExpr pre lvs (subst unifier <$> absType ty e)
  where -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        -- !!! HACK: When inserting the replacement expression for an     !!!
        -- !!! abstracted function, we have to unify the original         !!!
        -- !!! function type with the instantiated function type in order !!!
        -- !!! to obtain a type substitution that can then be applied to  !!!
        -- !!! the type annotations in the replacement expression.        !!!
        -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        absType ty' (Variable spi _ v') = Variable spi ty' v'
        absType ty' (Apply   spi e1 e2) =
          Apply spi (absType (TypeArrow (typeOf e2) ty') e1) e2
        absType _ _ = internalError "Lift.absExpr.absType"
absExpr _   _   c@(Constructor _ _ _) = return c
absExpr pre lvs (Apply       spi e1 e2) = Apply spi <$> absExpr pre lvs e1
                                                    <*> absExpr pre lvs e2
absExpr pre lvs (Let          _ _ ds e) = absDeclGroup pre lvs ds e
absExpr pre lvs (Case      _ _ ct e bs) =
  mkCase ct <$> absExpr pre lvs e <*> mapM (absAlt pre lvs) bs
absExpr pre lvs (Typed        spi e ty) =
  flip (Typed spi) ty <$> absExpr pre lvs e
absExpr _   _   e                   = internalError $ "Lift.absExpr: " ++ show e

absAlt :: String -> [Ident] -> Alt Type -> LiftM (Alt Type)
absAlt pre lvs (Alt p t rhs) = Alt p t <$> absRhs pre lvs' rhs
  where lvs' = lvs ++ bv t

-- -----------------------------------------------------------------------------
-- Lifting
-- -----------------------------------------------------------------------------

-- After the abstraction pass, all local function declarations are lifted
-- to the top-level.

liftFunDecl :: Eq a => Decl a -> [Decl a]
liftFunDecl (FunctionDecl p a f eqs) =
  FunctionDecl p a f eqs' : map renameFunDecl (concat dss')
  where (eqs', dss') = unzip $ map liftEquation eqs
liftFunDecl d                        = [d]

liftVarDecl :: Eq a => Decl a -> (Decl a, [Decl a])
liftVarDecl (PatternDecl   p t rhs) = (PatternDecl p t rhs', ds')
  where (rhs', ds') = liftRhs rhs
liftVarDecl ex@(FreeDecl       _ _) = (ex, [])
liftVarDecl _ = error "Lift.liftVarDecl: no pattern match"

liftEquation :: Eq a => Equation a -> (Equation a, [Decl a])
liftEquation (Equation p a lhs rhs) = (Equation p a lhs rhs', ds')
  where (rhs', ds') = liftRhs rhs

liftRhs :: Eq a => Rhs a -> (Rhs a, [Decl a])
liftRhs (SimpleRhs p _ e _) = first (simpleRhs p) (liftExpr e)
liftRhs _                   = error "Lift.liftRhs: no pattern match"

liftDeclGroup :: Eq a => [Decl a] -> ([Decl a], [Decl a])
liftDeclGroup ds = (vds', concat (map liftFunDecl fds ++ dss'))
  where (fds , vds ) = partition isFunDecl ds
        (vds', dss') = unzip $ map liftVarDecl vds

liftExpr :: Eq a => Expression a -> (Expression a, [Decl a])
liftExpr l@(Literal     _ _ _) = (l, [])
liftExpr v@(Variable    _ _ _) = (v, [])
liftExpr c@(Constructor _ _ _) = (c, [])
liftExpr (Apply       spi e1 e2) = (Apply spi e1' e2', ds1 ++ ds2)
  where (e1', ds1) = liftExpr e1
        (e2', ds2) = liftExpr e2
liftExpr (Let        _ _ ds e) = (mkLet ds' e', ds1 ++ ds2)
  where (ds', ds1) = liftDeclGroup ds
        (e' , ds2) = liftExpr e
liftExpr (Case    _ _ ct e alts) = (mkCase ct e' alts', concat $ ds' : dss')
  where (e'   , ds' ) = liftExpr e
        (alts', dss') = unzip $ map liftAlt alts
liftExpr (Typed        spi e ty) =
  (Typed spi e' ty, ds) where (e', ds) = liftExpr e
liftExpr _ = internalError "Lift.liftExpr"

liftAlt :: Eq a => Alt a -> (Alt a, [Decl a])
liftAlt (Alt p t rhs) = (Alt p t rhs', ds') where (rhs', ds') = liftRhs rhs

-- -----------------------------------------------------------------------------
-- Renaming
-- -----------------------------------------------------------------------------

-- After all local function declarations have been lifted to top-level, we
-- may have to rename duplicate function arguments. Due to polymorphic let
-- declarations it could happen that an argument was added multiple times
-- instantiated with different types during the abstraction pass beforehand.

type RenameMap a = [((a, Ident), Ident)]

renameFunDecl :: Eq a => Decl a -> Decl a
renameFunDecl (FunctionDecl p a f eqs) =
  FunctionDecl p a f (map renameEquation eqs)
renameFunDecl d                        = d

renameEquation :: Eq a => Equation a -> Equation a
renameEquation (Equation p a lhs rhs) = Equation p a lhs' (renameRhs rm rhs)
  where (rm, lhs') = renameLhs lhs

renameLhs :: Eq a => Lhs a -> (RenameMap a, Lhs a)
renameLhs (FunLhs spi f ts) = (rm, FunLhs spi f ts')
  where (rm, ts') = foldr renamePattern ([], []) ts
renameLhs _             = error "Lift.renameLhs"

renamePattern :: Eq a => Pattern a -> (RenameMap a, [Pattern a])
              -> (RenameMap a, [Pattern a])
renamePattern (VariablePattern spi a v) (rm, ts)
  | v `elem` varPatNames ts =
    let v' = updIdentName (++ ("." ++ show (length rm))) v
    in  (((a, v), v') : rm, VariablePattern spi a v' : ts)
renamePattern t                     (rm, ts) = (rm, t : ts)

renameRhs :: Eq a => RenameMap a -> Rhs a -> Rhs a
renameRhs rm (SimpleRhs p _ e _) = simpleRhs p (renameExpr rm e)
renameRhs _  _                   = error "Lift.renameRhs"

renameExpr :: Eq a => RenameMap a -> Expression a -> Expression a
renameExpr _  l@(Literal       _ _ _) = l
renameExpr rm v@(Variable   spi a v')
  | isQualified v' = v
  | otherwise      = case lookup (a, unqualify v') rm of
                       Just v'' -> Variable spi a (qualify v'')
                       _        -> v
renameExpr _  c@(Constructor _ _ _) = c
renameExpr rm (Typed       spi e ty) = Typed spi (renameExpr rm e) ty
renameExpr rm (Apply       spi e1 e2) =
  Apply spi (renameExpr rm e1) (renameExpr rm e2)
renameExpr rm (Let       _ _ ds e) =
  mkLet (map (renameDecl rm) ds) (renameExpr rm e)
renameExpr rm (Case    _ _ ct e alts) =
  mkCase ct (renameExpr rm e) (map (renameAlt rm) alts)
renameExpr _  _                   = error "Lift.renameExpr"

renameDecl :: Eq a => RenameMap a -> Decl a -> Decl a
renameDecl rm (PatternDecl p t rhs) = PatternDecl p t (renameRhs rm rhs)
renameDecl _  d                     = d

renameAlt :: Eq a => RenameMap a -> Alt a -> Alt a
renameAlt rm (Alt p t rhs) = Alt p t (renameRhs rm rhs)

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

isFunDecl :: Decl a -> Bool
isFunDecl (FunctionDecl _ _ _ _) = True
isFunDecl (ExternalDecl _ _    ) = True
isFunDecl _                      = False

mkFun :: ModuleIdent -> String -> a -> Ident -> Expression a
mkFun m pre a = Variable NoSpanInfo a . qualifyWith m . liftIdent pre

liftIdent :: String -> Ident -> Ident
liftIdent prefix x = renameIdent (mkIdent $ prefix ++ showIdent x) $ idUnique x

varPatNames :: [Pattern a] -> [Ident]
varPatNames = mapMaybe varPatName

varPatName :: Pattern a -> Maybe Ident
varPatName (VariablePattern _ _ i) = Just i
varPatName _                     = Nothing

dummyType :: Type
dummyType = TypeForall [] undefined

isDummyType :: Type -> Bool
isDummyType (TypeForall [] _) = True
isDummyType _                 = False
