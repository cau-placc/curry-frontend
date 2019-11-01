{- |
  Module      :  $Header$
  Description :  Deriving instances
  Copyright   :  (c) 2016        Finn Teegen
  License     :  BSD-3-clause

  Maintainer  :  bjp@informatik.uni-kiel.de
  Stability   :  experimental
  Portability :  portable

  TODO
-}
{-# LANGUAGE CPP #-}
module Transformations.Derive (derive) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>))
#endif
import qualified Control.Monad.State as S (State, evalState, gets, modify)
import           Data.List         (intercalate, intersperse)
import           Data.Maybe        (fromJust, isJust)
import qualified Data.Set   as Set (deleteMin, union)

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax

import Base.CurryTypes (fromPredType)
import Base.Messages (internalError)
import Base.Types
import Base.TypeSubst (instanceType)
import Base.Typing (typeOf)
import Base.Utils (snd3, mapAccumM)

import Env.Instance
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

data DVState = DVState
  { moduleIdent :: ModuleIdent
  , tyConsEnv   :: TCEnv
  , valueEnv    :: ValueEnv
  , instEnv     :: InstEnv
  , opPrecEnv   :: OpPrecEnv
  , nextId      :: Integer
  }

type DVM = S.State DVState

derive :: TCEnv -> ValueEnv -> InstEnv -> OpPrecEnv -> Module Type
       -> Module Type
derive tcEnv vEnv inEnv pEnv (Module spi ps m es is ds) = Module spi ps m es is $
  ds ++ concat (S.evalState (mapM deriveInstances tds) initState)
  where tds = filter isTypeDecl ds
        initState = DVState m tcEnv vEnv inEnv pEnv 1

getModuleIdent :: DVM ModuleIdent
getModuleIdent = S.gets moduleIdent

getTyConsEnv :: DVM TCEnv
getTyConsEnv = S.gets tyConsEnv

getValueEnv :: DVM ValueEnv
getValueEnv = S.gets valueEnv

getInstEnv :: DVM InstEnv
getInstEnv = S.gets instEnv

getPrecEnv :: DVM OpPrecEnv
getPrecEnv = S.gets opPrecEnv

getNextId :: DVM Integer
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

-- TODO: Comment (here and below)

type ConstrInfo = (Int, QualIdent, Maybe [Ident], [Type])

-- An instance declaration is created for each type class of a deriving clause.
-- Newtype declaration are simply treated as data declarations.

deriveInstances :: Decl Type -> DVM [Decl Type]
deriveInstances (DataDecl    _ tc tvs _ clss) = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  let otc = qualifyWith m tc
      cis = constructors m otc tcEnv
  mapM (deriveInstance otc tvs cis) clss
deriveInstances (NewtypeDecl p tc tvs _ clss) =
  deriveInstances $ DataDecl p tc tvs [] clss
deriveInstances _                             = return []

deriveInstance :: QualIdent -> [Ident] -> [ConstrInfo] -> QualIdent
               -> DVM (Decl Type)
deriveInstance tc tvs cis cls = do
  inEnv <- getInstEnv
  let ps = snd3 $ fromJust $ lookupInstInfo (cls, tc) inEnv
      ty = applyType (TypeConstructor tc) $
             take (length tvs) $ map TypeVariable [0 ..]
      ContextType _ cx inst = fromPredType tvs $ TypeContext ps ty
  ds <- deriveMethods cls ty cis ps
  return $ InstanceDecl NoSpanInfo cx cls inst ds

-- Note: The methods and arities of the generated instance declarations have to
-- correspond to the methods and arities entered previously into the instance
-- environment (see instance check).

deriveMethods :: QualIdent -> Type -> [ConstrInfo] -> PredSet
              -> DVM [Decl Type]
deriveMethods cls
  | cls == qEqId      = deriveEqMethods
  | cls == qOrdId     = deriveOrdMethods
  | cls == qEnumId    = deriveEnumMethods
  | cls == qBoundedId = deriveBoundedMethods
  | cls == qReadId    = deriveReadMethods
  | cls == qShowId    = deriveShowMethods
  | otherwise         = internalError $ "Derive.deriveMethods: " ++ show cls

-- Binary Operators:

type BinOpExpr = Int
              -> [Expression Type]
              -> Int
              -> [Expression Type]
              -> Expression Type

deriveBinOp :: QualIdent -> Ident -> BinOpExpr -> Type -> [ConstrInfo]
            -> PredSet -> DVM (Decl Type)
deriveBinOp cls op expr ty cis ps = do
  pty <- getInstMethodType ps cls ty op
  eqs <- mapM (deriveBinOpEquation op expr ty) $ sequence [cis, cis]
  return $ FunctionDecl NoSpanInfo pty op eqs

deriveBinOpEquation :: Ident -> BinOpExpr -> Type -> [ConstrInfo]
                    -> DVM (Equation Type)
deriveBinOpEquation op expr ty [(i1, c1, _, tys1), (i2, c2, _, tys2)] = do
  vs1 <- mapM (freshArgument . instType) tys1
  vs2 <- mapM (freshArgument . instType) tys2
  let pat1 = constrPattern pty c1 vs1
      pat2 = constrPattern pty c2 vs2
      es1 = map (uncurry mkVar) vs1
      es2 = map (uncurry mkVar) vs2
  return $ mkEquation NoSpanInfo op [pat1, pat2] $ expr i1 es1 i2 es2
  where pty = instType ty
deriveBinOpEquation _ _ _ _ = internalError "Derive.deriveBinOpEquation"

-- Equality:

deriveEqMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl Type]
deriveEqMethods ty cis ps = sequence
  [deriveBinOp qEqId eqOpId eqOpExpr ty cis ps]

eqOpExpr :: BinOpExpr
eqOpExpr i1 es1 i2 es2
  | i1 == i2  = if null es1 then prelTrue
                            else foldl1 prelAnd $ zipWith prelEq es1 es2
  | otherwise = prelFalse

-- Ordering:

deriveOrdMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl Type]
deriveOrdMethods ty cis ps = sequence
  [deriveBinOp qOrdId leqOpId leqOpExpr ty cis ps]

leqOpExpr :: BinOpExpr
leqOpExpr i1 es1 i2 es2
  | i1 < i2   = prelTrue
  | i1 > i2   = prelFalse
  | otherwise = if null es1 then prelTrue
                            else foldl1 prelOr $ map innerAnd [0 .. n - 1]
  where n = length es1
        innerAnd i = foldl1 prelAnd $ map (innerOp i) [0 .. i]
        innerOp i j | j == n - 1 = prelLeq (es1 !! j) (es2 !! j)
                    | j == i     = prelLt  (es1 !! j) (es2 !! j)
                    | otherwise  = prelEq  (es1 !! j) (es2 !! j)

-- Enumerations:

deriveEnumMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl Type]
deriveEnumMethods ty cis ps = sequence
  [ deriveSuccOrPred succId ty cis (tail cis) ps
  , deriveSuccOrPred predId ty (tail cis) cis ps
  , deriveToEnum ty cis ps
  , deriveFromEnum ty cis ps
  , deriveEnumFrom ty (last cis) ps
  , deriveEnumFromThen ty (head cis) (last cis) ps
  ]

deriveSuccOrPred :: Ident -> Type -> [ConstrInfo] -> [ConstrInfo] -> PredSet
                 -> DVM (Decl Type)
deriveSuccOrPred f ty cis1 cis2 ps = do
  pty <- getInstMethodType ps qEnumId ty f
  FunctionDecl NoSpanInfo pty f <$> if null eqs
                                 then do
                                        v <- freshArgument $ instType ty
                                        return [failedEquation f ty v]
                                 else return eqs
  where eqs = zipWith (succOrPredEquation f ty) cis1 cis2

succOrPredEquation :: Ident -> Type -> ConstrInfo -> ConstrInfo
                   -> Equation Type
succOrPredEquation f ty (_, c1, _, _) (_, c2, _, _) =
  mkEquation NoSpanInfo f [ConstructorPattern NoSpanInfo pty c1 []] $
    Constructor NoSpanInfo pty c2
  where pty = instType ty

failedEquation :: Ident -> Type -> (Type, Ident) -> Equation Type
failedEquation f ty v =
  mkEquation NoSpanInfo f [uncurry (VariablePattern NoSpanInfo) v] $
    preludeFailed $ instType ty

deriveToEnum :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl Type)
deriveToEnum ty cis ps = do
  pty <- getInstMethodType ps qEnumId ty toEnumId
  return $ FunctionDecl NoSpanInfo pty toEnumId eqs
  where eqs = zipWith (toEnumEquation ty) [0 ..] cis

toEnumEquation :: Type -> Integer -> ConstrInfo -> Equation Type
toEnumEquation ty i (_, c, _, _) =
  mkEquation NoSpanInfo toEnumId
    [LiteralPattern NoSpanInfo (intType) (Int i)] $
    Constructor NoSpanInfo (instType ty) c

deriveFromEnum :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl Type)
deriveFromEnum ty cis ps = do
  pty <- getInstMethodType ps qEnumId ty fromEnumId
  return $ FunctionDecl NoSpanInfo pty fromEnumId eqs
  where eqs = zipWith (fromEnumEquation ty) cis [0 ..]

fromEnumEquation :: Type -> ConstrInfo -> Integer -> Equation Type
fromEnumEquation ty (_, c, _, _) i =
  mkEquation NoSpanInfo fromEnumId [ConstructorPattern NoSpanInfo pty c []] $
    Literal NoSpanInfo (intType) $ Int i
  where pty = instType ty

deriveEnumFrom :: Type -> ConstrInfo -> PredSet -> DVM (Decl Type)
deriveEnumFrom ty (_, c, _, _) ps = do
  pty <- getInstMethodType ps qEnumId ty enumFromId
  v <- freshArgument $ instType ty
  return $ funDecl NoSpanInfo pty enumFromId
    [uncurry (VariablePattern NoSpanInfo) v] $
    enumFromExpr v c

enumFromExpr :: (Type, Ident) -> QualIdent -> Expression Type
enumFromExpr v c = prelEnumFromTo (uncurry mkVar v) $
  Constructor NoSpanInfo (fst v) c

deriveEnumFromThen :: Type -> ConstrInfo -> ConstrInfo -> PredSet
                   -> DVM (Decl Type)
deriveEnumFromThen ty (_, c1, _, _) (_, c2, _, _) ps = do
  pty <- getInstMethodType ps qEnumId ty enumFromId
  vs  <- mapM (freshArgument . instType) $ replicate 2 ty
  let [v1, v2] = vs
  return $ funDecl NoSpanInfo pty enumFromThenId
    (map (uncurry (VariablePattern NoSpanInfo)) vs) $
    enumFromThenExpr v1 v2 c1 c2

enumFromThenExpr :: (Type, Ident) -> (Type, Ident) -> QualIdent
                 -> QualIdent -> Expression Type
enumFromThenExpr v1 v2 c1 c2 =
  prelEnumFromThenTo (uncurry mkVar v1) (uncurry mkVar v2) $ boundedExpr
  where boundedExpr = IfThenElse NoSpanInfo
                                 (prelLeq
                                   (prelFromEnum $ uncurry mkVar v1)
                                   (prelFromEnum $ uncurry mkVar v2))
                                 (Constructor NoSpanInfo (fst v1) c2)
                                 (Constructor NoSpanInfo (fst v1) c1)

-- Upper and Lower Bounds:

deriveBoundedMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl Type]
deriveBoundedMethods ty cis ps = sequence
  [ deriveMaxOrMinBound qMinBoundId ty (head cis) ps
  , deriveMaxOrMinBound qMaxBoundId ty (last cis) ps
  ]

deriveMaxOrMinBound :: QualIdent -> Type -> ConstrInfo -> PredSet
                    -> DVM (Decl Type)
deriveMaxOrMinBound f ty (_, c, _, tys) ps = do
  pty <- getInstMethodType ps qBoundedId ty $ unqualify f
  return $ funDecl NoSpanInfo pty (unqualify f) [] $ maxOrMinBoundExpr f c ty tys

maxOrMinBoundExpr :: QualIdent -> QualIdent -> Type -> [Type]
                  -> Expression Type
maxOrMinBoundExpr f c ty tys =
  apply (Constructor NoSpanInfo pty c) $
  map (flip (Variable NoSpanInfo) f) instTys
  where instTy:instTys = map instType $ ty : tys
        pty = foldr TypeArrow instTy instTys

-- Read:

deriveReadMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl Type]
deriveReadMethods ty cis ps = sequence [deriveReadsPrec ty cis ps]

deriveReadsPrec :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl Type)
deriveReadsPrec ty cis ps = do
  pty <- getInstMethodType ps qReadId ty $ readsPrecId
  d <- freshArgument intType
  r <- freshArgument stringType
  let pats = map (uncurry (VariablePattern NoSpanInfo)) [d, r]
  funDecl NoSpanInfo pty readsPrecId pats <$>
    deriveReadsPrecExpr ty cis (uncurry mkVar d) (uncurry mkVar r)

deriveReadsPrecExpr :: Type -> [ConstrInfo] -> Expression Type
                    -> Expression Type -> DVM (Expression Type)
deriveReadsPrecExpr ty cis d r = do
  es <- mapM (deriveReadsPrecReadParenExpr ty d) cis
  return $ foldr1 prelAppend $ map (flip (Apply NoSpanInfo) r) $ es

deriveReadsPrecReadParenExpr :: Type -> Expression Type -> ConstrInfo
                             -> DVM (Expression Type)
deriveReadsPrecReadParenExpr ty d ci@(_, c, _, _) = do
  pEnv <- getPrecEnv
  let p = precedence c pEnv
  e <- deriveReadsPrecLambdaExpr ty ci p
  return $ prelReadParen (readsPrecReadParenCondExpr ci d p) e

readsPrecReadParenCondExpr :: ConstrInfo -> Expression Type -> Precedence
                           -> Expression Type
readsPrecReadParenCondExpr (_, c, _, tys) d p
  | null tys                        = prelFalse
  | isQInfixOp c && length tys == 2 =
    prelLt (Literal NoSpanInfo intType $ Int p) d
  | otherwise                       =
    prelLt (Literal NoSpanInfo intType $ Int 10) d

deriveReadsPrecLambdaExpr :: Type -> ConstrInfo -> Precedence
                      -> DVM (Expression Type)
deriveReadsPrecLambdaExpr ty (_, c, ls, tys) p = do
  r <- freshArgument stringType
  (stmts, vs, s) <- deriveReadsPrecStmts (unqualify c) (p + 1) r ls tys
  let pty = foldr TypeArrow (instType ty) $ map instType tys
      e = Tuple NoSpanInfo
                [ apply (Constructor NoSpanInfo pty c) $ map (uncurry mkVar) vs
                , uncurry mkVar s
                ]
  return $ Lambda NoSpanInfo [uncurry (VariablePattern NoSpanInfo) r]
         $ ListCompr NoSpanInfo e stmts

deriveReadsPrecStmts
  :: Ident -> Precedence -> (Type, Ident) -> Maybe [Ident] -> [Type]
  -> DVM ([Statement Type], [(Type, Ident)], (Type, Ident))
deriveReadsPrecStmts c p r ls tys
  | null tys                       = deriveReadsPrecNullaryConstrStmts c r
  | isJust ls                      =
    deriveReadsPrecRecordConstrStmts c r (fromJust ls) tys
  | isInfixOp c && length tys == 2 = deriveReadsPrecInfixConstrStmts c p r tys
  | otherwise                      = deriveReadsPrecConstrStmts c r tys

deriveReadsPrecNullaryConstrStmts
  :: Ident -> (Type, Ident)
  -> DVM ([Statement Type], [(Type, Ident)], (Type, Ident))
deriveReadsPrecNullaryConstrStmts c r = do
  (s, stmt) <- deriveReadsPrecLexStmt (idName c) r
  return ([stmt], [], s)

deriveReadsPrecRecordConstrStmts
  :: Ident -> (Type, Ident) -> [Ident] -> [Type]
  -> DVM ([Statement Type], [(Type, Ident)], (Type, Ident))
deriveReadsPrecRecordConstrStmts c r ls tys = do
  (s, stmt1) <- deriveReadsPrecLexStmt (idName c) r
  (t, ress) <-
    mapAccumM deriveReadsPrecFieldStmts s $ zip3 ("{" : repeat ",") ls tys
  let (stmtss, vs) = unzip ress
  (u, stmt2) <- deriveReadsPrecLexStmt "}" t
  return (stmt1 : concat stmtss ++ [stmt2], vs, u)

deriveReadsPrecFieldStmts
  :: (Type, Ident) -> (String, Ident, Type)
  -> DVM ((Type, Ident), ([Statement Type], (Type, Ident)))
deriveReadsPrecFieldStmts r (pre, l, ty) = do
  (s, stmt1) <- deriveReadsPrecLexStmt pre r
  (t, stmt2) <- deriveReadsPrecLexStmt (idName l) s
  (u, stmt3) <- deriveReadsPrecLexStmt "=" t
  (w, (stmt4, v)) <- deriveReadsPrecReadsPrecStmt 0 u ty
  return (w, ([stmt1, stmt2, stmt3, stmt4], v))

deriveReadsPrecInfixConstrStmts
  :: Ident -> Precedence -> (Type, Ident) -> [Type]
  -> DVM ([Statement Type], [(Type, Ident)], (Type, Ident))
deriveReadsPrecInfixConstrStmts c p r tys = do
  (s, (stmt1, v1)) <- deriveReadsPrecReadsPrecStmt (p + 1) r $ head tys
  (t, stmt2) <- deriveReadsPrecLexStmt (idName c) s
  (u, (stmt3, v2)) <- deriveReadsPrecReadsPrecStmt (p + 1) t $ head $ tail tys
  return ([stmt1, stmt2, stmt3], [v1, v2], u)

deriveReadsPrecConstrStmts
  :: Ident -> (Type, Ident) -> [Type]
  -> DVM ([Statement Type], [(Type, Ident)], (Type, Ident))
deriveReadsPrecConstrStmts c r tys = do
    (s, stmt) <- deriveReadsPrecLexStmt (idName c) r
    (t, ress) <- mapAccumM (deriveReadsPrecReadsPrecStmt 11) s tys
    let (stmts, vs) = unzip ress
    return (stmt : stmts, vs, t)

deriveReadsPrecLexStmt :: String -> (Type, Ident)
                      -> DVM ((Type, Ident), Statement Type)
deriveReadsPrecLexStmt str r = do
  s <- freshArgument $ stringType
  let pat  = TuplePattern NoSpanInfo
               [ LiteralPattern NoSpanInfo stringType $ String str
               , uncurry (VariablePattern NoSpanInfo) s
               ]
      stmt = StmtBind NoSpanInfo pat $ preludeLex $ uncurry mkVar r
  return (s, stmt)

deriveReadsPrecReadsPrecStmt  :: Precedence -> (Type, Ident) -> Type
      -> DVM ((Type, Ident), (Statement Type, (Type, Ident)))
deriveReadsPrecReadsPrecStmt p r ty = do
  v <- freshArgument $ instType ty
  s <- freshArgument $ stringType
  let pat  = TuplePattern NoSpanInfo $
               map (uncurry (VariablePattern NoSpanInfo)) [v, s]
      stmt = StmtBind NoSpanInfo pat $ preludeReadsPrec (instType ty) p $
               uncurry mkVar r
  return (s, (stmt, v))

-- Show:

deriveShowMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl Type]
deriveShowMethods ty cis ps = sequence [deriveShowsPrec ty cis ps]

deriveShowsPrec :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl Type)
deriveShowsPrec ty cis ps = do
  pty <- getInstMethodType ps qShowId ty $ showsPrecId
  eqs <- mapM (deriveShowsPrecEquation ty) cis
  return $ FunctionDecl NoSpanInfo pty showsPrecId eqs

deriveShowsPrecEquation :: Type -> ConstrInfo -> DVM (Equation Type)
deriveShowsPrecEquation ty (_, c, ls, tys) = do
  d <- freshArgument intType
  vs <- mapM (freshArgument . instType) tys
  let pats = [uncurry (VariablePattern NoSpanInfo) d, constrPattern pty c vs]
  pEnv <- getPrecEnv
  return $ mkEquation NoSpanInfo showsPrecId pats $ showsPrecExpr (unqualify c)
    (precedence c pEnv) ls (uncurry mkVar d) $ map (uncurry mkVar) vs
  where pty = instType ty

showsPrecExpr :: Ident -> Precedence -> Maybe [Ident] -> Expression Type
              -> [Expression Type] -> Expression Type
showsPrecExpr c p ls d vs
  | null vs                       = showsPrecNullaryConstrExpr c
  | isJust ls                     = showsPrecShowParenExpr d 10 $
    showsPrecRecordConstrExpr c (fromJust ls) vs
  | isInfixOp c && length vs == 2 = showsPrecShowParenExpr d p $
    showsPrecInfixConstrExpr c p vs
  | otherwise                     = showsPrecShowParenExpr d 10 $
    showsPrecConstrExpr c vs

showsPrecNullaryConstrExpr :: Ident -> Expression Type
showsPrecNullaryConstrExpr c = preludeShowString $ showsConstr c ""

showsPrecShowParenExpr :: Expression Type -> Precedence
                       -> Expression Type -> Expression Type
showsPrecShowParenExpr d p =
  prelShowParen $ prelLt (Literal NoSpanInfo intType $ Int p) d

showsPrecRecordConstrExpr :: Ident -> [Ident] -> [Expression Type]
                          -> Expression Type
showsPrecRecordConstrExpr c ls vs = foldr prelDot (preludeShowString "}") $
  (:) (preludeShowString $ showsConstr c " {") $
    intercalate [preludeShowString ", "] $ zipWith showsPrecFieldExpr ls vs

showsPrecFieldExpr :: Ident -> Expression Type -> [Expression Type]
showsPrecFieldExpr l v =
  [preludeShowString $ showsConstr l " = ", preludeShowsPrec 0 v]

showsPrecInfixConstrExpr :: Ident -> Precedence -> [Expression Type]
                         -> Expression Type
showsPrecInfixConstrExpr c p vs = foldr1 prelDot
  [ preludeShowsPrec (p + 1) $ head vs
  , preludeShowString $ ' ' : idName c ++ " "
  , preludeShowsPrec (p + 1) $ head $ tail vs
  ]

showsPrecConstrExpr :: Ident -> [Expression Type] -> Expression Type
showsPrecConstrExpr c vs = foldr1 prelDot $
  preludeShowString (showsConstr c " ") :
    intersperse (preludeShowString " ") (map (preludeShowsPrec 11) vs)

-- -----------------------------------------------------------------------------
-- Generating variables
-- -----------------------------------------------------------------------------

freshArgument :: Type -> DVM (Type, Ident)
freshArgument = freshVar "_#arg"

freshVar :: String -> Type -> DVM (Type, Ident)
freshVar name ty =
  ((,) ty) . mkIdent . (name ++) .  show <$> getNextId

-- -----------------------------------------------------------------------------
-- Auxiliary functions
-- -----------------------------------------------------------------------------

constructors :: ModuleIdent -> QualIdent -> TCEnv -> [ConstrInfo]
constructors m tc tcEnv =  zipWith (mkConstrInfo m) [1 ..] $
  case qualLookupTypeInfo tc tcEnv of
    [DataType     _ _ cs] -> cs
    [RenamingType _ _ nc] -> [nc]
    _                     -> internalError $ "Derive.constructors: " ++ show tc

mkConstrInfo :: ModuleIdent -> Int -> DataConstr -> ConstrInfo
mkConstrInfo m i (DataConstr   c    tys) =
  (i, qualifyWith m c, Nothing, tys)
mkConstrInfo m i (RecordConstr c ls tys) =
  (i, qualifyWith m c, Just ls, tys)

showsConstr :: Ident -> ShowS
showsConstr c = showParen (isInfixOp c) $ showString $ idName c

precedence :: QualIdent -> OpPrecEnv -> Precedence
precedence op pEnv = case qualLookupP op pEnv of
  [] -> defaultPrecedence
  PrecInfo _ (OpPrec _ p) : _ -> p

instType :: Type -> Type
instType (TypeConstructor tc) = TypeConstructor tc
instType (TypeVariable    tv) = TypeVariable (-1 - tv)
instType (TypeApply  ty1 ty2) = TypeApply (instType ty1) (instType ty2)
instType (TypeArrow  ty1 ty2) = TypeArrow (instType ty1) (instType ty2)
instType ty = ty

-- Returns the type for a given instance's method of a given class. To this
-- end, the class method's type is stripped of its first predicate (which is
-- the implicit class constraint) and the class variable is replaced with the
-- instance's type. The remaining predicate set is then united with the
-- instance's predicate set.

getInstMethodType :: PredSet -> QualIdent -> Type -> Ident -> DVM Type
getInstMethodType ps cls ty f = do
  vEnv <- getValueEnv
  return $ instMethodType vEnv ps cls ty f

instMethodType :: ValueEnv -> PredSet -> QualIdent -> Type -> Ident -> Type
instMethodType vEnv ps cls ty f = TypeContext (ps `Set.union` ps'') ty''
  where TypeContext ps' ty' = case qualLookupValue (qualifyLike cls f) vEnv of
          [Value _ _ _ pty] -> rawPredType pty
          _ -> internalError $ "Derive.instMethodType"
        TypeContext ps'' ty'' = instanceType ty $ TypeContext (Set.deleteMin ps') ty'

-- -----------------------------------------------------------------------------
-- Prelude entities
-- -----------------------------------------------------------------------------

prelTrue :: Expression Type
prelTrue = Constructor NoSpanInfo boolType qTrueId

prelFalse :: Expression Type
prelFalse = Constructor NoSpanInfo boolType qFalseId

prelAppend :: Expression Type -> Expression Type -> Expression Type
prelAppend e1 e2 = foldl1 (Apply NoSpanInfo)
  [Variable NoSpanInfo pty qAppendOpId, e1, e2]
  where pty = foldr1 TypeArrow $ replicate 3 $ typeOf e1

prelDot :: Expression Type -> Expression Type -> Expression Type
prelDot e1 e2 = foldl1 (Apply NoSpanInfo)
  [Variable NoSpanInfo pty qDotOpId, e1, e2]
  where ty1@(TypeArrow _    ty12) = typeOf e1
        ty2@(TypeArrow ty21 _   ) = typeOf e2
        pty = foldr1 TypeArrow [ty1, ty2, ty21, ty12]

prelAnd :: Expression Type -> Expression Type -> Expression Type
prelAnd e1 e2 = foldl1 (Apply NoSpanInfo)
  [Variable NoSpanInfo pty qAndOpId, e1, e2]
  where pty = foldr1 TypeArrow $ replicate 3 boolType

prelEq :: Expression Type -> Expression Type -> Expression Type
prelEq e1 e2 = foldl1 (Apply NoSpanInfo)
  [Variable NoSpanInfo pty qEqOpId, e1, e2]
  where ty = typeOf e1
        pty =  foldr1 TypeArrow [ty, ty, boolType]

prelLeq :: Expression Type -> Expression Type -> Expression Type
prelLeq e1 e2 = foldl1 (Apply NoSpanInfo)
  [Variable NoSpanInfo pty qLeqOpId, e1, e2]
  where ty = typeOf e1
        pty = foldr1 TypeArrow [ty, ty, boolType]

prelLt :: Expression Type -> Expression Type -> Expression Type
prelLt e1 e2 = foldl1 (Apply NoSpanInfo)
  [Variable NoSpanInfo pty qLtOpId, e1, e2]
  where ty = typeOf e1
        pty = foldr1 TypeArrow [ty, ty, boolType]

prelOr :: Expression Type -> Expression Type -> Expression Type
prelOr e1 e2 = foldl1 (Apply NoSpanInfo)
  [Variable NoSpanInfo pty qOrOpId, e1, e2]
  where pty = foldr1 TypeArrow $ replicate 3 boolType

prelFromEnum :: Expression Type -> Expression Type
prelFromEnum e = Apply NoSpanInfo (Variable NoSpanInfo pty qFromEnumId) e
  where pty = TypeArrow (typeOf e) intType

prelEnumFromTo :: Expression Type -> Expression Type
               -> Expression Type
prelEnumFromTo e1 e2 = apply (Variable NoSpanInfo pty qEnumFromToId) [e1, e2]
  where ty = typeOf e1
        pty = foldr1 TypeArrow [ty, ty, listType ty]

prelEnumFromThenTo :: Expression Type -> Expression Type
                   -> Expression Type -> Expression Type
prelEnumFromThenTo e1 e2 e3 =
  apply (Variable NoSpanInfo pty qEnumFromThenToId) [e1, e2, e3]
  where ty = typeOf e1
        pty = foldr1 TypeArrow [ty, ty, ty, listType ty]

prelReadParen :: Expression Type -> Expression Type
              -> Expression Type
prelReadParen e1 e2 = apply (Variable NoSpanInfo pty qReadParenId) [e1, e2]
  where ty = typeOf e2
        pty = foldr1 TypeArrow [boolType, ty, ty]

prelShowParen :: Expression Type -> Expression Type
              -> Expression Type
prelShowParen e1 e2 = apply (Variable NoSpanInfo pty qShowParenId) [e1, e2]
  where pty = foldr1 TypeArrow [ boolType
                               , TypeArrow stringType stringType
                               , stringType, stringType
                               ]

preludeLex :: Expression Type -> Expression Type
preludeLex e = Apply NoSpanInfo (Variable NoSpanInfo pty qLexId) e
  where pty = TypeArrow stringType $
                listType $ tupleType [stringType, stringType]

preludeReadsPrec :: Type -> Integer -> Expression Type
                 -> Expression Type
preludeReadsPrec ty p e = flip (Apply NoSpanInfo) e $
  Apply NoSpanInfo (Variable NoSpanInfo pty qReadsPrecId) $
  Literal NoSpanInfo intType $ Int p
  where pty = foldr1 TypeArrow [ intType, stringType
                               , listType $ tupleType [ ty
                                                      , stringType
                                                      ]
                               ]

preludeShowsPrec :: Integer -> Expression Type -> Expression Type
preludeShowsPrec p e = flip (Apply NoSpanInfo) e $
  Apply NoSpanInfo (Variable NoSpanInfo pty qShowsPrecId) $
  Literal NoSpanInfo intType $ Int p
  where pty = foldr1 TypeArrow [ intType, typeOf e
                               , stringType, stringType
                               ]

preludeShowString :: String -> Expression Type
preludeShowString s = Apply NoSpanInfo (Variable NoSpanInfo pty qShowStringId) $
  Literal NoSpanInfo stringType $ String s
  where pty = foldr1 TypeArrow $ replicate 3 stringType

preludeFailed :: Type -> Expression Type
preludeFailed ty = Variable NoSpanInfo ty qFailedId
