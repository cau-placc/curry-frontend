{- |
    Module      :  $Header$
    Description :  Proper Qualification
    Copyright   :  (c) 2001 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    After checking the module and before starting the translation into the
    intermediate language, the compiler properly qualifies all type
    constructors, data constructors and (global) functions
    occurring in a pattern or expression such that their module prefix
    matches the module of their definition.
    This is done also for functions and constructors declared
    in the current module.
    Only functions and variables declared in local declarations groups
    as well as function arguments remain unchanged.
-}
{-# LANGUAGE CPP #-}
module Transformations.Qual (qual) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative       ((<$>), (<*>), pure)
#endif
import qualified Control.Monad.Reader as R (Reader, asks, runReader)
import           Data.Traversable
import           Prelude hiding            (mapM)

import Curry.Base.Ident
import Curry.Syntax

import Base.TopEnv         (origName)

import Env.TypeConstructor (TCEnv   , qualLookupTypeInfo)
import Env.Value           (ValueEnv, qualLookupValue)

data QualEnv = QualEnv
  { moduleIdent :: ModuleIdent
  , tyConsEnv   :: TCEnv
  , valueEnv    :: ValueEnv
  }

type Qual a = a -> R.Reader QualEnv a

qual :: ModuleIdent -> TCEnv -> ValueEnv -> Module a -> Module a
qual m tcEnv tyEnv mdl = R.runReader (qModule mdl) (QualEnv m tcEnv tyEnv)

qModule :: Qual (Module a)
qModule (Module spi li ps m es is ds) = do
  es' <- qExportSpec es
  ds' <- mapM qDecl  ds
  return (Module spi li ps m es' is ds')

qExportSpec :: Qual (Maybe ExportSpec)
qExportSpec Nothing                 = return Nothing
qExportSpec (Just (Exporting p es)) = (Just . Exporting p) <$> mapM qExport es

qExport :: Qual Export
qExport (Export            spi x) = Export spi <$> qIdent x
qExport (ExportTypeWith spi t cs) = flip (ExportTypeWith spi) cs <$> qConstr t
qExport (ExportTypeAll     spi t) = ExportTypeAll spi <$> qConstr t
qExport m@(ExportModule      _ _) = return m

qDecl :: Qual (Decl a)
qDecl i@(InfixDecl              _ _ _ _) = return i
qDecl (DataDecl          p n vs cs clss) = DataDecl p n vs <$>
  mapM qConstrDecl cs <*> mapM qClass clss
qDecl e@(ExternalDataDecl         _ _ _) = return e
qDecl (NewtypeDecl       p n vs nc clss) = NewtypeDecl p n vs <$>
  qNewConstrDecl nc <*> mapM qClass clss
qDecl (TypeDecl               p n vs ty) = TypeDecl p n vs <$> qTypeExpr ty
qDecl (TypeSig                 p fs qty) = TypeSig p fs <$> qQualTypeExpr qty
qDecl (FunctionDecl           a p f eqs) = FunctionDecl a p f <$> mapM qEquation eqs
qDecl e@(ExternalDecl               _ _) = return e
qDecl (PatternDecl              p t rhs) = PatternDecl p <$> qPattern t <*> qRhs rhs
qDecl vs@(FreeDecl                  _ _) = return vs
qDecl (DefaultDecl                p tys) = DefaultDecl p <$> mapM qTypeExpr tys
qDecl (ClassDecl p li cx cls tvs fds ds) = ClassDecl p li <$>
  qContext cx <*> pure cls <*> pure tvs <*> pure fds <*> mapM qDecl ds
qDecl (InstanceDecl p li cx qcls tys ds) = InstanceDecl p li <$>
  qContext cx <*> qClass qcls <*> mapM qTypeExpr tys <*> mapM qDecl ds

qConstrDecl :: Qual ConstrDecl
qConstrDecl (ConstrDecl p      n tys) =
  ConstrDecl p n <$> mapM qTypeExpr tys
qConstrDecl (ConOpDecl  p ty1 op ty2) =
  ConOpDecl p <$> qTypeExpr ty1 <*> pure op <*> qTypeExpr ty2
qConstrDecl (RecordDecl p       c fs) =
  RecordDecl p c <$> mapM qFieldDecl fs

qNewConstrDecl :: Qual NewConstrDecl
qNewConstrDecl (NewConstrDecl p n ty)
  = NewConstrDecl p n <$> qTypeExpr ty
qNewConstrDecl (NewRecordDecl p n (f, ty))
  = (\ty' -> NewRecordDecl p n (f, ty')) <$> qTypeExpr ty

qFieldDecl :: Qual FieldDecl
qFieldDecl (FieldDecl p fs ty) = FieldDecl p fs <$> qTypeExpr ty

qConstraint :: Qual Constraint
qConstraint (Constraint spi cls tys) =
  Constraint spi <$> qClass cls <*> mapM qTypeExpr tys

qContext :: Qual Context
qContext = mapM qConstraint

qTypeExpr :: Qual TypeExpr
qTypeExpr (ConstructorType     spi c) = ConstructorType spi <$> qConstr c
qTypeExpr (ApplyType     spi ty1 ty2) = ApplyType spi <$> qTypeExpr ty1
                                              <*> qTypeExpr ty2
qTypeExpr v@(VariableType        _ _) = return v
qTypeExpr (TupleType         spi tys) = TupleType spi <$> mapM qTypeExpr tys
qTypeExpr (ListType           spi ty) = ListType spi  <$> qTypeExpr ty
qTypeExpr (ArrowType     spi ty1 ty2) = ArrowType spi <$> qTypeExpr ty1
                                              <*> qTypeExpr ty2
qTypeExpr (ParenType          spi ty) = ParenType spi <$> qTypeExpr ty
qTypeExpr (ForallType      spi vs ty) = ForallType spi vs <$> qTypeExpr ty

qQualTypeExpr :: Qual QualTypeExpr
qQualTypeExpr (QualTypeExpr spi cx ty) = QualTypeExpr spi <$> qContext cx
                                                          <*> qTypeExpr ty

qEquation :: Qual (Equation a)
qEquation (Equation p lhs rhs) = Equation p <$> qLhs lhs <*> qRhs rhs

qLhs :: Qual (Lhs a)
qLhs (FunLhs sp    f ts) = FunLhs sp       f  <$> mapM qPattern ts
qLhs (OpLhs sp t1 op t2) = flip (OpLhs sp) op <$> qPattern t1 <*> qPattern t2
qLhs (ApLhs sp   lhs ts) = ApLhs sp           <$> qLhs lhs <*> mapM qPattern ts

qPattern :: Qual (Pattern a)
qPattern l@(LiteralPattern          _ _ _) = return l
qPattern n@(NegativePattern         _ _ _) = return n
qPattern v@(VariablePattern         _ _ _) = return v
qPattern (ConstructorPattern   spi a c ts) =
  ConstructorPattern spi a <$> qIdent c <*> mapM qPattern ts
qPattern (InfixPattern     spi a t1 op t2) =
  InfixPattern spi a <$> qPattern t1 <*> qIdent op <*> qPattern t2
qPattern (ParenPattern              spi t) = ParenPattern spi <$> qPattern t
qPattern (RecordPattern        spi a c fs) = RecordPattern spi a <$> qIdent c
                                          <*> mapM (qField qPattern) fs
qPattern (TuplePattern             spi ts) =
  TuplePattern spi <$> mapM qPattern ts
qPattern (ListPattern            spi a ts) =
  ListPattern spi a <$> mapM qPattern ts
qPattern (AsPattern               spi v t) = AsPattern spi v <$> qPattern t
qPattern (LazyPattern               spi t) = LazyPattern spi <$> qPattern t
qPattern (FunctionPattern      spi a f ts) =
  FunctionPattern spi a <$> qIdent f <*> mapM qPattern ts
qPattern (InfixFuncPattern spi a t1 op t2) =
  InfixFuncPattern spi a <$> qPattern t1 <*> qIdent op <*> qPattern t2

qRhs :: Qual (Rhs a)
qRhs (SimpleRhs spi li e ds) =
  SimpleRhs  spi li <$> qExpr e           <*> mapM qDecl ds
qRhs (GuardedRhs spi li es ds) =
  GuardedRhs spi li <$> mapM qCondExpr es <*> mapM qDecl ds

qCondExpr :: Qual (CondExpr a)
qCondExpr (CondExpr p g e) = CondExpr p <$> qExpr g <*> qExpr e

qExpr :: Qual (Expression a)
qExpr l@(Literal             _ _ _) = return l
qExpr (Variable            spi a v) = Variable     spi a <$> qIdent v
qExpr (Constructor         spi a c) = Constructor  spi a <$> qIdent c
qExpr (Paren                 spi e) = Paren        spi   <$> qExpr e
qExpr (Typed             spi e qty) = Typed        spi   <$> qExpr e
                                                         <*> qQualTypeExpr qty
qExpr (Record           spi a c fs) =
  Record spi a <$> qIdent c <*> mapM (qField qExpr) fs
qExpr (RecordUpdate       spi e fs) =
  RecordUpdate spi <$> qExpr e <*> mapM (qField qExpr) fs
qExpr (Tuple                spi es) = Tuple          spi <$> mapM qExpr es
qExpr (List               spi a es) = List           spi a <$> mapM qExpr es
qExpr (ListCompr          spi e qs) = ListCompr      spi <$> qExpr e
                                                         <*> mapM qStmt qs
qExpr (EnumFrom              spi e) = EnumFrom       spi <$> qExpr e
qExpr (EnumFromThen      spi e1 e2) = EnumFromThen   spi <$> qExpr e1
                                                         <*> qExpr e2
qExpr (EnumFromTo        spi e1 e2) = EnumFromTo     spi <$> qExpr e1
                                                         <*> qExpr e2
qExpr (EnumFromThenTo spi e1 e2 e3) = EnumFromThenTo spi <$> qExpr e1
                                                         <*> qExpr e2
                                                         <*> qExpr e3
qExpr (UnaryMinus            spi e) = UnaryMinus     spi <$> qExpr e
qExpr (Apply             spi e1 e2) = Apply          spi <$> qExpr e1
                                                         <*> qExpr e2
qExpr (InfixApply     spi e1 op e2) = InfixApply     spi <$> qExpr e1
                                                         <*> qInfixOp op
                                                         <*> qExpr e2
qExpr (LeftSection        spi e op) = LeftSection  spi <$> qExpr e
                                                       <*> qInfixOp op
qExpr (RightSection       spi op e) = RightSection spi <$> qInfixOp op
                                                       <*> qExpr e
qExpr (Lambda             spi ts e) = Lambda       spi <$> mapM qPattern ts
                                                       <*> qExpr e
qExpr (Let             spi li ds e) = Let spi li <$> mapM qDecl ds  <*> qExpr e
qExpr (Do             spi li sts e) = Do  spi li <$> mapM qStmt sts <*> qExpr e
qExpr (IfThenElse     spi e1 e2 e3) = IfThenElse spi <$> qExpr e1 <*> qExpr e2
                                                     <*> qExpr e3
qExpr (Case         spi li ct e as) = Case spi li ct <$> qExpr e <*> mapM qAlt as

qStmt :: Qual (Statement a)
qStmt (StmtExpr spi     e) = StmtExpr spi    <$> qExpr e
qStmt (StmtBind spi t   e) = StmtBind spi    <$> qPattern t <*> qExpr e
qStmt (StmtDecl spi li ds) = StmtDecl spi li <$> mapM qDecl ds

qAlt :: Qual (Alt a)
qAlt (Alt p t rhs) = Alt p <$> qPattern t <*> qRhs rhs

qField :: Qual a -> Qual (Field a)
qField q (Field p l x) = Field p <$> qIdent l <*> q x

qInfixOp :: Qual (InfixOp a)
qInfixOp (InfixOp     a op) = InfixOp     a <$> qIdent op
qInfixOp (InfixConstr a op) = InfixConstr a <$> qIdent op

qIdent :: Qual QualIdent
qIdent x | isQualified x                = x'
         | hasGlobalScope (unqualify x) = x'
         | otherwise                    = return x
  where
  x' = do
    m     <- R.asks moduleIdent
    tyEnv <- R.asks valueEnv
    return $ case qualLookupValue x tyEnv of
      [y] -> origName y
      _   -> case qualLookupValue qmx tyEnv of
        [y] -> origName y
        _   -> qmx
        where qmx = qualQualify m x

qConstr :: Qual QualIdent
qConstr x = do
  m     <- R.asks moduleIdent
  tcEnv <- R.asks tyConsEnv
  return $ case qualLookupTypeInfo x tcEnv of
    [y] -> origName y
    _   -> case qualLookupTypeInfo qmx tcEnv of
      [y] -> origName y
      _   -> qmx
      where qmx = qualQualify m x

qClass :: Qual QualIdent
qClass = qConstr
