{- |
  Module      :  $Header$
  Description :  Deriving instances
  Copyright   :  (c) 2016        Finn Teegen
  License     :  OtherLicense

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
import           Control.Monad.ListM      (mapAccumM)
import qualified Control.Monad.State as S (State, evalState, gets, modify)
import           Data.List         (intercalate, intersperse)
import           Data.Maybe        (fromJust, isJust)
import qualified Data.Set   as Set (deleteMin, union)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.CurryTypes (fromPredType)
import Base.Messages (internalError)
import Base.Types
import Base.TypeSubst (instanceType)
import Base.Typing (typeOf)
import Base.Utils (snd3)

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

derive :: TCEnv -> ValueEnv -> InstEnv -> OpPrecEnv -> Module PredType
       -> Module PredType
derive tcEnv vEnv inEnv pEnv (Module ps m es is ds) = Module ps m es is $
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

deriveInstances :: Decl PredType -> DVM [Decl PredType]
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
               -> DVM (Decl PredType)
deriveInstance tc tvs cis cls = do
  inEnv <- getInstEnv
  let ps = snd3 $ fromJust $ lookupInstInfo (cls, tc) inEnv
      ty = applyType (TypeConstructor tc) $
             take (length tvs) $ map TypeVariable [0 ..]
      QualTypeExpr cx inst = fromPredType tvs $ PredType ps ty
  ds <- deriveMethods cls ty cis ps
  return $ InstanceDecl NoPos cx cls inst ds

-- Note: The methods and arities of the generated instance declarations have to
-- correspond to the methods and arities entered previously into the instance
-- environment (see instance check).

deriveMethods :: QualIdent -> Type -> [ConstrInfo] -> PredSet
              -> DVM [Decl PredType]
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
              -> [Expression PredType]
              -> Int
              -> [Expression PredType]
              -> Expression PredType

deriveBinOp :: QualIdent -> Ident -> BinOpExpr -> Type -> [ConstrInfo]
            -> PredSet -> DVM (Decl PredType)
deriveBinOp cls op expr ty cis ps = do
  pty <- getInstMethodType ps cls ty op
  eqs <- mapM (deriveBinOpEquation op expr ty) $ sequence [cis, cis]
  return $ FunctionDecl NoPos pty op eqs

deriveBinOpEquation :: Ident -> BinOpExpr -> Type -> [ConstrInfo]
                    -> DVM (Equation PredType)
deriveBinOpEquation op expr ty [(i1, c1, _, tys1), (i2, c2, _, tys2)] = do
  vs1 <- mapM (freshArgument . instType) tys1
  vs2 <- mapM (freshArgument . instType) tys2
  let pat1 = constrPattern pty c1 vs1
      pat2 = constrPattern pty c2 vs2
      es1 = map (uncurry mkVar) vs1
      es2 = map (uncurry mkVar) vs2
  return $ mkEquation NoPos op [pat1, pat2] $ expr i1 es1 i2 es2
  where pty = predType $ instType ty
deriveBinOpEquation _ _ _ _ = internalError "Derive.deriveBinOpEquation"

-- Equality:

deriveEqMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl PredType]
deriveEqMethods ty cis ps = sequence
  [deriveBinOp qEqId eqOpId eqOpExpr ty cis ps]

eqOpExpr :: BinOpExpr
eqOpExpr i1 es1 i2 es2
  | i1 == i2  = if null es1 then prelTrue
                            else foldl1 prelAnd $ zipWith prelEq es1 es2
  | otherwise = prelFalse

-- Ordering:

deriveOrdMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl PredType]
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

deriveEnumMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl PredType]
deriveEnumMethods ty cis ps = sequence
  [ deriveSuccOrPred succId ty cis (tail cis) ps
  , deriveSuccOrPred predId ty (tail cis) cis ps
  , deriveToEnum ty cis ps
  , deriveFromEnum ty cis ps
  , deriveEnumFrom ty (last cis) ps
  , deriveEnumFromThen ty (head cis) (last cis) ps
  ]

deriveSuccOrPred :: Ident -> Type -> [ConstrInfo] -> [ConstrInfo] -> PredSet
                 -> DVM (Decl PredType)
deriveSuccOrPred f ty cis1 cis2 ps = do
  pty <- getInstMethodType ps qEnumId ty f
  FunctionDecl NoPos pty f <$> if null eqs
                                 then do
                                        v <- freshArgument $ instType ty
                                        return [failedEquation f ty v]
                                 else return eqs
  where eqs = zipWith (succOrPredEquation f ty) cis1 cis2

succOrPredEquation :: Ident -> Type -> ConstrInfo -> ConstrInfo
                   -> Equation PredType
succOrPredEquation f ty (_, c1, _, _) (_, c2, _, _) =
  mkEquation NoPos f [ConstructorPattern pty c1 []] $ Constructor pty c2
  where pty = predType $ instType ty

failedEquation :: Ident -> Type -> (PredType, Ident) -> Equation PredType
failedEquation f ty v =
  mkEquation NoPos f [uncurry VariablePattern v] $ preludeFailed $ instType ty

deriveToEnum :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl PredType)
deriveToEnum ty cis ps = do
  pty <- getInstMethodType ps qEnumId ty toEnumId
  return $ FunctionDecl NoPos pty toEnumId eqs
  where eqs = zipWith (toEnumEquation ty) [0 ..] cis

toEnumEquation :: Type -> Integer -> ConstrInfo -> Equation PredType
toEnumEquation ty i (_, c, _, _) =
  mkEquation NoPos toEnumId [LiteralPattern (predType intType) (Int i)] $
    Constructor (predType $ instType ty) c

deriveFromEnum :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl PredType)
deriveFromEnum ty cis ps = do
  pty <- getInstMethodType ps qEnumId ty fromEnumId
  return $ FunctionDecl NoPos pty fromEnumId eqs
  where eqs = zipWith (fromEnumEquation ty) cis [0 ..]

fromEnumEquation :: Type -> ConstrInfo -> Integer -> Equation PredType
fromEnumEquation ty (_, c, _, _) i =
  mkEquation NoPos fromEnumId [ConstructorPattern pty c []] $
    Literal (predType intType) $ Int i
  where pty = predType $ instType ty

deriveEnumFrom :: Type -> ConstrInfo -> PredSet -> DVM (Decl PredType)
deriveEnumFrom ty (_, c, _, _) ps = do
  pty <- getInstMethodType ps qEnumId ty enumFromId
  v <- freshArgument $ instType ty
  return $ funDecl NoPos pty enumFromId [uncurry VariablePattern v] $
    enumFromExpr v c

enumFromExpr :: (PredType, Ident) -> QualIdent -> Expression PredType
enumFromExpr v c = prelEnumFromTo (uncurry mkVar v) $ Constructor (fst v) c

deriveEnumFromThen :: Type -> ConstrInfo -> ConstrInfo -> PredSet
                   -> DVM (Decl PredType)
deriveEnumFromThen ty (_, c1, _, _) (_, c2, _, _) ps = do
  pty <- getInstMethodType ps qEnumId ty enumFromId
  vs@[v1, v2] <- mapM (freshArgument . instType) $ replicate 2 ty
  return $ funDecl NoPos pty enumFromThenId (map (uncurry VariablePattern) vs) $
    enumFromThenExpr v1 v2 c1 c2

enumFromThenExpr :: (PredType, Ident) -> (PredType, Ident) -> QualIdent
                 -> QualIdent -> Expression PredType
enumFromThenExpr v1 v2 c1 c2 =
  prelEnumFromThenTo (uncurry mkVar v1) (uncurry mkVar v2) $ boundedExpr
  where boundedExpr = IfThenElse (prelLeq
                                   (prelFromEnum $ uncurry mkVar v1)
                                   (prelFromEnum $ uncurry mkVar v2))
                                 (Constructor (fst v1) c2)
                                 (Constructor (fst v1) c1)

-- Upper and Lower Bounds:

deriveBoundedMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl PredType]
deriveBoundedMethods ty cis ps = sequence
  [ deriveMaxOrMinBound qMaxBoundId ty (head cis) ps
  , deriveMaxOrMinBound qMinBoundId ty (last cis) ps
  ]

deriveMaxOrMinBound :: QualIdent -> Type -> ConstrInfo -> PredSet
                    -> DVM (Decl PredType)
deriveMaxOrMinBound f ty (_, c, _, tys) ps = do
  pty <- getInstMethodType ps qBoundedId ty $ unqualify f
  return $ funDecl NoPos pty (unqualify f) [] $ maxOrMinBoundExpr f c ty tys

maxOrMinBoundExpr :: QualIdent -> QualIdent -> Type -> [Type]
                  -> Expression PredType
maxOrMinBoundExpr f c ty tys =
  apply (Constructor pty c) $ map (flip Variable f . predType) instTys
  where instTy:instTys = map instType $ ty : tys
        pty = predType $ foldr TypeArrow instTy instTys

-- Read:

deriveReadMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl PredType]
deriveReadMethods ty cis ps = sequence [deriveReadsPrec ty cis ps]

deriveReadsPrec :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl PredType)
deriveReadsPrec ty cis ps = do
  pty <- getInstMethodType ps qReadId ty $ readsPrecId
  d <- freshArgument intType
  r <- freshArgument stringType
  let pats = map (uncurry VariablePattern) [d, r]
  funDecl NoPos pty readsPrecId pats <$>
    deriveReadsPrecExpr ty cis (uncurry mkVar d) (uncurry mkVar r)

deriveReadsPrecExpr :: Type -> [ConstrInfo] -> Expression PredType
                    -> Expression PredType -> DVM (Expression PredType)
deriveReadsPrecExpr ty cis d r = do
  es <- mapM (deriveReadsPrecReadParenExpr ty d) cis
  return $ foldr1 prelAppend $ map (flip Apply r) $ es

deriveReadsPrecReadParenExpr :: Type -> Expression PredType -> ConstrInfo
                             -> DVM (Expression PredType)
deriveReadsPrecReadParenExpr ty d ci@(_, c, _, _) = do
  pEnv <- getPrecEnv
  let p = precedence c pEnv
  e <- deriveReadsPrecLambdaExpr ty ci p
  return $ prelReadParen (readsPrecReadParenCondExpr ci d p) e

readsPrecReadParenCondExpr :: ConstrInfo -> Expression PredType -> Precedence
                           -> Expression PredType
readsPrecReadParenCondExpr (_, c, _, tys) d p
  | null tys                        = prelFalse
  | isQInfixOp c && length tys == 2 =
    prelLt (Literal predIntType $ Int p) d
  | otherwise                       =
    prelLt (Literal predIntType $ Int 10) d

deriveReadsPrecLambdaExpr :: Type -> ConstrInfo -> Precedence
                      -> DVM (Expression PredType)
deriveReadsPrecLambdaExpr ty (_, c, ls, tys) p = do
  r <- freshArgument stringType
  (stmts, vs, s) <- deriveReadsPrecStmts (unqualify c) (p + 1) r ls tys
  let pty = predType $ foldr TypeArrow (instType ty) $ map instType tys
      e = Tuple [ apply (Constructor pty c) $ map (uncurry mkVar) vs
                , uncurry mkVar s
                ]
  return $ Lambda [uncurry VariablePattern r] $ ListCompr e stmts

deriveReadsPrecStmts
  :: Ident -> Precedence -> (PredType, Ident) -> Maybe [Ident] -> [Type]
  -> DVM ([Statement PredType], [(PredType, Ident)], (PredType, Ident))
deriveReadsPrecStmts c p r ls tys
  | null tys                       = deriveReadsPrecNullaryConstrStmts c r
  | isJust ls                      =
    deriveReadsPrecRecordConstrStmts c r (fromJust ls) tys
  | isInfixOp c && length tys == 2 = deriveReadsPrecInfixConstrStmts c p r tys
  | otherwise                      = deriveReadsPrecConstrStmts c r tys

deriveReadsPrecNullaryConstrStmts
  :: Ident -> (PredType, Ident)
  -> DVM ([Statement PredType], [(PredType, Ident)], (PredType, Ident))
deriveReadsPrecNullaryConstrStmts c r = do
  (s, stmt) <- deriveReadsPrecLexStmt (idName c) r
  return ([stmt], [], s)

deriveReadsPrecRecordConstrStmts
  :: Ident -> (PredType, Ident) -> [Ident] -> [Type]
  -> DVM ([Statement PredType], [(PredType, Ident)], (PredType, Ident))
deriveReadsPrecRecordConstrStmts c r ls tys = do
  (s, stmt1) <- deriveReadsPrecLexStmt (idName c) r
  (t, ress) <-
    mapAccumM deriveReadsPrecFieldStmts s $ zip3 ("{" : repeat ",") ls tys
  let (stmtss, vs) = unzip ress
  (u, stmt2) <- deriveReadsPrecLexStmt "}" t
  return (stmt1 : concat stmtss ++ [stmt2], vs, u)

deriveReadsPrecFieldStmts
  :: (PredType, Ident) -> (String, Ident, Type)
  -> DVM ((PredType, Ident), ([Statement PredType], (PredType, Ident)))
deriveReadsPrecFieldStmts r (pre, l, ty) = do
  (s, stmt1) <- deriveReadsPrecLexStmt pre r
  (t, stmt2) <- deriveReadsPrecLexStmt (idName l) s
  (u, stmt3) <- deriveReadsPrecLexStmt "=" t
  (w, (stmt4, v)) <- deriveReadsPrecReadsPrecStmt 0 u ty
  return (w, ([stmt1, stmt2, stmt3, stmt4], v))

deriveReadsPrecInfixConstrStmts
  :: Ident -> Precedence -> (PredType, Ident) -> [Type]
  -> DVM ([Statement PredType], [(PredType, Ident)], (PredType, Ident))
deriveReadsPrecInfixConstrStmts c p r tys = do
  (s, (stmt1, v1)) <- deriveReadsPrecReadsPrecStmt (p + 1) r $ head tys
  (t, stmt2) <- deriveReadsPrecLexStmt (idName c) s
  (u, (stmt3, v2)) <- deriveReadsPrecReadsPrecStmt (p + 1) t $ head $ tail tys
  return ([stmt1, stmt2, stmt3], [v1, v2], u)

deriveReadsPrecConstrStmts
  :: Ident -> (PredType, Ident) -> [Type]
  -> DVM ([Statement PredType], [(PredType, Ident)], (PredType, Ident))
deriveReadsPrecConstrStmts c r tys = do
    (s, stmt) <- deriveReadsPrecLexStmt (idName c) r
    (t, ress) <- mapAccumM (deriveReadsPrecReadsPrecStmt 11) s tys
    let (stmts, vs) = unzip ress
    return (stmt : stmts, vs, t)

deriveReadsPrecLexStmt :: String -> (PredType, Ident)
                      -> DVM ((PredType, Ident), Statement PredType)
deriveReadsPrecLexStmt str r = do
  s <- freshArgument $ stringType
  let pat  = TuplePattern
               [ LiteralPattern predStringType $ String str
               , uncurry VariablePattern s
               ]
      stmt = StmtBind pat $ preludeLex $ uncurry mkVar r
  return (s, stmt)

deriveReadsPrecReadsPrecStmt  :: Precedence -> (PredType, Ident) -> Type
      -> DVM ((PredType, Ident), (Statement PredType, (PredType, Ident)))
deriveReadsPrecReadsPrecStmt p r ty = do
  v <- freshArgument $ instType ty
  s <- freshArgument $ stringType
  let pat  = TuplePattern $ map (uncurry VariablePattern) [v, s]
      stmt = StmtBind pat $ preludeReadsPrec (instType ty) p $
               uncurry mkVar r
  return (s, (stmt, v))

-- Show:

deriveShowMethods :: Type -> [ConstrInfo] -> PredSet -> DVM [Decl PredType]
deriveShowMethods ty cis ps = sequence [deriveShowsPrec ty cis ps]

deriveShowsPrec :: Type -> [ConstrInfo] -> PredSet -> DVM (Decl PredType)
deriveShowsPrec ty cis ps = do
  pty <- getInstMethodType ps qShowId ty $ showsPrecId
  eqs <- mapM (deriveShowsPrecEquation ty) cis
  return $ FunctionDecl NoPos pty showsPrecId eqs

deriveShowsPrecEquation :: Type -> ConstrInfo -> DVM (Equation PredType)
deriveShowsPrecEquation ty (_, c, ls, tys) = do
  d <- freshArgument intType
  vs <- mapM (freshArgument . instType) tys
  let pats = [uncurry VariablePattern d, constrPattern pty c vs]
  pEnv <- getPrecEnv
  return $ mkEquation NoPos showsPrecId pats $ showsPrecExpr (unqualify c)
    (precedence c pEnv) ls (uncurry mkVar d) $ map (uncurry mkVar) vs
  where pty = predType $ instType ty

showsPrecExpr :: Ident -> Precedence -> Maybe [Ident] -> Expression PredType
              -> [Expression PredType] -> Expression PredType
showsPrecExpr c p ls d vs
  | null vs                       = showsPrecNullaryConstrExpr c
  | isJust ls                     = showsPrecShowParenExpr d 10 $
    showsPrecRecordConstrExpr c (fromJust ls) vs
  | isInfixOp c && length vs == 2 = showsPrecShowParenExpr d p $
    showsPrecInfixConstrExpr c p vs
  | otherwise                     = showsPrecShowParenExpr d 10 $
    showsPrecConstrExpr c vs

showsPrecNullaryConstrExpr :: Ident -> Expression PredType
showsPrecNullaryConstrExpr c = preludeShowString $ showsConstr c ""

showsPrecShowParenExpr :: Expression PredType -> Precedence
                       -> Expression PredType -> Expression PredType
showsPrecShowParenExpr d p =
  prelShowParen $ prelLt (Literal predIntType $ Int p) d

showsPrecRecordConstrExpr :: Ident -> [Ident] -> [Expression PredType]
                          -> Expression PredType
showsPrecRecordConstrExpr c ls vs = foldr prelDot (preludeShowString "}") $
  (:) (preludeShowString $ showsConstr c " {") $
    intercalate [preludeShowString ", "] $ zipWith showsPrecFieldExpr ls vs

showsPrecFieldExpr :: Ident -> Expression PredType -> [Expression PredType]
showsPrecFieldExpr l v =
  [preludeShowString $ showsConstr l " = ", preludeShowsPrec 0 v]

showsPrecInfixConstrExpr :: Ident -> Precedence -> [Expression PredType]
                         -> Expression PredType
showsPrecInfixConstrExpr c p vs = foldr1 prelDot
  [ preludeShowsPrec (p + 1) $ head vs
  , preludeShowString $ ' ' : idName c ++ " "
  , preludeShowsPrec (p + 1) $ head $ tail vs
  ]

showsPrecConstrExpr :: Ident -> [Expression PredType] -> Expression PredType
showsPrecConstrExpr c vs = foldr1 prelDot $
  preludeShowString (showsConstr c " ") :
    intersperse (preludeShowString " ") (map (preludeShowsPrec 11) vs)

-- -----------------------------------------------------------------------------
-- Generating variables
-- -----------------------------------------------------------------------------

freshArgument :: Type -> DVM (PredType, Ident)
freshArgument = freshVar "_#arg"

freshVar :: String -> Type -> DVM (PredType, Ident)
freshVar name ty =
  ((,) (predType ty)) . mkIdent . (name ++) .  show <$> getNextId

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
mkConstrInfo m i (DataConstr   c _ _    tys) =
  (i, qualifyWith m c, Nothing, tys)
mkConstrInfo m i (RecordConstr c _ _ ls tys) =
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

getInstMethodType :: PredSet -> QualIdent -> Type -> Ident -> DVM PredType
getInstMethodType ps cls ty f = do
  vEnv <- getValueEnv
  return $ instMethodType vEnv ps cls ty f

instMethodType :: ValueEnv -> PredSet -> QualIdent -> Type -> Ident -> PredType
instMethodType vEnv ps cls ty f = PredType (ps `Set.union` ps'') ty''
  where PredType ps' ty' = case qualLookupValue (qualifyLike cls f) vEnv of
          [Value _ _ _ (ForAll _ pty)] -> pty
          _ -> internalError $ "Derive.instMethodType"
        PredType ps'' ty'' = instanceType ty $ PredType (Set.deleteMin ps') ty'

-- -----------------------------------------------------------------------------
-- Prelude entities
-- -----------------------------------------------------------------------------

prelTrue :: Expression PredType
prelTrue = Constructor predBoolType qTrueId

prelFalse :: Expression PredType
prelFalse = Constructor predBoolType qFalseId

prelAppend :: Expression PredType -> Expression PredType -> Expression PredType
prelAppend e1 e2 = foldl1 Apply [Variable pty qAppendOpId, e1, e2]
  where pty = predType $ foldr1 TypeArrow $ replicate 3 $ typeOf e1

prelDot :: Expression PredType -> Expression PredType -> Expression PredType
prelDot e1 e2 = foldl1 Apply [Variable pty qDotOpId, e1, e2]
  where ty1@(TypeArrow _    ty12) = typeOf e1
        ty2@(TypeArrow ty21 _   ) = typeOf e2
        pty = predType $ foldr1 TypeArrow [ty1, ty2, ty21, ty12]

prelAnd :: Expression PredType -> Expression PredType -> Expression PredType
prelAnd e1 e2 = foldl1 Apply [Variable pty qAndOpId, e1, e2]
  where pty = predType $ foldr1 TypeArrow $ replicate 3 boolType

prelEq :: Expression PredType -> Expression PredType -> Expression PredType
prelEq e1 e2 = foldl1 Apply [Variable pty qEqOpId, e1, e2]
  where ty = typeOf e1
        pty = predType $ foldr1 TypeArrow [ty, ty, boolType]

prelLeq :: Expression PredType -> Expression PredType -> Expression PredType
prelLeq e1 e2 = foldl1 Apply [Variable pty qLeqOpId, e1, e2]
  where ty = typeOf e1
        pty = predType $ foldr1 TypeArrow [ty, ty, boolType]

prelLt :: Expression PredType -> Expression PredType -> Expression PredType
prelLt e1 e2 = foldl1 Apply [Variable pty qLtOpId, e1, e2]
  where ty = typeOf e1
        pty = predType $ foldr1 TypeArrow [ty, ty, boolType]

prelOr :: Expression PredType -> Expression PredType -> Expression PredType
prelOr e1 e2 = foldl1 Apply [Variable pty qOrOpId, e1, e2]
  where pty = predType $ foldr1 TypeArrow $ replicate 3 boolType

prelFromEnum :: Expression PredType -> Expression PredType
prelFromEnum e = Apply (Variable pty qFromEnumId) e
  where pty = predType $ TypeArrow (typeOf e) intType

prelEnumFromTo :: Expression PredType -> Expression PredType
               -> Expression PredType
prelEnumFromTo e1 e2 = apply (Variable pty qEnumFromToId) [e1, e2]
  where ty = typeOf e1
        pty = predType $ foldr1 TypeArrow [ty, ty, listType ty]

prelEnumFromThenTo :: Expression PredType -> Expression PredType
                   -> Expression PredType -> Expression PredType
prelEnumFromThenTo e1 e2 e3 =
  apply (Variable pty qEnumFromThenToId) [e1, e2, e3]
  where ty = typeOf e1
        pty = predType $ foldr1 TypeArrow [ty, ty, ty, listType ty]

prelReadParen :: Expression PredType -> Expression PredType
              -> Expression PredType
prelReadParen e1 e2 = apply (Variable pty qReadParenId) [e1, e2]
  where ty = typeOf e2
        pty = predType $ foldr1 TypeArrow [boolType, ty, ty]

prelShowParen :: Expression PredType -> Expression PredType
              -> Expression PredType
prelShowParen e1 e2 = apply (Variable pty qShowParenId) [e1, e2]
  where pty = predType $ foldr1 TypeArrow [ boolType
                                          , TypeArrow stringType stringType
                                          , stringType, stringType
                                          ]

preludeLex :: Expression PredType -> Expression PredType
preludeLex e = Apply (Variable pty qLexId) e
  where pty = predType $ TypeArrow stringType $
                listType $ tupleType [stringType, stringType]

preludeReadsPrec :: Type -> Integer -> Expression PredType
                 -> Expression PredType
preludeReadsPrec ty p e = flip Apply e $
  Apply (Variable pty qReadsPrecId) $ Literal predIntType $ Int p
  where pty = predType $ foldr1 TypeArrow [ intType, stringType
                                          , listType $ tupleType [ ty
                                                                 , stringType
                                                                 ]
                                          ]

preludeShowsPrec :: Integer -> Expression PredType -> Expression PredType
preludeShowsPrec p e = flip Apply e $
  Apply (Variable pty qShowsPrecId) $ Literal predIntType $ Int p
  where pty = predType $ foldr1 TypeArrow [ intType, typeOf e
                                          , stringType, stringType
                                          ]

preludeShowString :: String -> Expression PredType
preludeShowString s = Apply (Variable pty qShowStringId) $
  Literal predStringType $ String s
  where pty = predType $ foldr1 TypeArrow $ replicate 3 stringType

preludeFailed :: Type -> Expression PredType
preludeFailed ty = Variable (predType ty) qFailedId
