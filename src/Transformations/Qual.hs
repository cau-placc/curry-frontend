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
qModule (Module ps m es is ds) = do
  es' <- qExportSpec es
  ds' <- mapM qDecl  ds
  return (Module ps m es' is ds')

qExportSpec :: Qual (Maybe ExportSpec)
qExportSpec Nothing                 = return Nothing
qExportSpec (Just (Exporting p es)) = (Just . Exporting p) <$> mapM qExport es

qExport :: Qual Export
qExport (Export            x) = Export <$> qIdent x
qExport (ExportTypeWith t cs) = flip ExportTypeWith cs <$> qConstr t
qExport (ExportTypeAll     t) = ExportTypeAll <$> qConstr t
qExport m@(ExportModule    _) = return m

qDecl :: Qual (Decl a)
qDecl i@(InfixDecl          _ _ _ _) = return i
qDecl (DataDecl      p n vs cs clss) = DataDecl p n vs <$>
  mapM qConstrDecl cs <*> mapM qClass clss
qDecl e@(ExternalDataDecl     _ _ _) = return e
qDecl (NewtypeDecl   p n vs nc clss) = NewtypeDecl p n vs <$>
  qNewConstrDecl nc <*> mapM qClass clss
qDecl (TypeDecl           p n vs ty) = TypeDecl p n vs <$> qTypeExpr ty
qDecl (TypeSig             p fs qty) = TypeSig p fs <$> qQualTypeExpr qty
qDecl (FunctionDecl       a p f eqs) = FunctionDecl a p f <$> mapM qEquation eqs
qDecl (ForeignDecl     p c x a n ty) = ForeignDecl p c x a n <$> qTypeExpr ty
qDecl e@(ExternalDecl           _ _) = return e
qDecl (PatternDecl          p t rhs) = PatternDecl p <$> qPattern t <*> qRhs rhs
qDecl vs@(FreeDecl              _ _) = return vs
qDecl (DefaultDecl            p tys) = DefaultDecl p <$> mapM qTypeExpr tys
qDecl (ClassDecl     p cx cls tv ds) = ClassDecl p <$>
  qContext cx <*> pure cls <*> pure tv <*> mapM qDecl ds
qDecl (InstanceDecl p cx qcls ty ds) = InstanceDecl p <$>
  qContext cx <*> qClass qcls <*> qTypeExpr ty <*> mapM qDecl ds

qConstrDecl :: Qual ConstrDecl
qConstrDecl (ConstrDecl p vs cx      n tys) =
  flip (ConstrDecl p vs) n <$> qContext cx <*> mapM qTypeExpr tys
qConstrDecl (ConOpDecl  p vs cx ty1 op ty2) =
  ConOpDecl p vs <$> qContext cx <*> qTypeExpr ty1 <*> pure op <*> qTypeExpr ty2
qConstrDecl (RecordDecl p vs cx       c fs) =
  flip (RecordDecl p vs) c <$> qContext cx <*> mapM qFieldDecl fs

qNewConstrDecl :: Qual NewConstrDecl
qNewConstrDecl (NewConstrDecl p n ty)
  = NewConstrDecl p n <$> qTypeExpr ty
qNewConstrDecl (NewRecordDecl p n (f, ty))
  = (\ty' -> NewRecordDecl p n (f, ty')) <$> qTypeExpr ty

qFieldDecl :: Qual FieldDecl
qFieldDecl (FieldDecl p fs ty) = FieldDecl p fs <$> qTypeExpr ty

qConstraint :: Qual Constraint
qConstraint (Constraint cls ty) = Constraint <$> qClass cls <*> qTypeExpr ty

qContext :: Qual Context
qContext = mapM qConstraint

qTypeExpr :: Qual TypeExpr
qTypeExpr (ConstructorType     c) = ConstructorType <$> qConstr c
qTypeExpr (ApplyType     ty1 ty2) = ApplyType <$> qTypeExpr ty1
                                              <*> qTypeExpr ty2
qTypeExpr v@(VariableType      _) = return v
qTypeExpr (TupleType         tys) = TupleType <$> mapM qTypeExpr tys
qTypeExpr (ListType           ty) = ListType  <$> qTypeExpr ty
qTypeExpr (ArrowType     ty1 ty2) = ArrowType <$> qTypeExpr ty1
                                              <*> qTypeExpr ty2
qTypeExpr (ParenType          ty) = ParenType <$> qTypeExpr ty
qTypeExpr (ForallType      vs ty) = ForallType vs <$> qTypeExpr ty

qQualTypeExpr :: Qual QualTypeExpr
qQualTypeExpr (QualTypeExpr cx ty) = QualTypeExpr <$> qContext cx
                                                  <*> qTypeExpr ty

qEquation :: Qual (Equation a)
qEquation (Equation p lhs rhs) = Equation p <$> qLhs lhs <*> qRhs rhs

qLhs :: Qual (Lhs a)
qLhs (FunLhs    f ts) = FunLhs f      <$> mapM qPattern ts
qLhs (OpLhs t1 op t2) = flip OpLhs op <$> qPattern t1 <*> qPattern t2
qLhs (ApLhs   lhs ts) = ApLhs         <$> qLhs lhs <*> mapM qPattern ts

qPattern :: Qual (Pattern a)
qPattern l@(LiteralPattern        _ _) = return l
qPattern n@(NegativePattern       _ _) = return n
qPattern v@(VariablePattern       _ _) = return v
qPattern (ConstructorPattern   a c ts) = ConstructorPattern a
                                         <$> qIdent c <*> mapM qPattern ts
qPattern (InfixPattern     a t1 op t2) = InfixPattern a <$> qPattern t1
                                                        <*> qIdent op
                                                        <*> qPattern t2
qPattern (ParenPattern              t) = ParenPattern <$> qPattern t
qPattern (RecordPattern        a c fs) = RecordPattern a <$> qIdent c
                                         <*> mapM (qField qPattern) fs
qPattern (TuplePattern             ts) = TuplePattern <$> mapM qPattern ts
qPattern (ListPattern            a ts) = ListPattern a <$> mapM qPattern ts
qPattern (AsPattern               v t) = AsPattern v <$> qPattern t
qPattern (LazyPattern               t) = LazyPattern <$> qPattern t
qPattern (FunctionPattern      a f ts) = FunctionPattern a <$> qIdent f
                                                           <*> mapM qPattern ts
qPattern (InfixFuncPattern a t1 op t2) = InfixFuncPattern a <$> qPattern t1
                                                            <*> qIdent op
                                                            <*> qPattern t2

qRhs :: Qual (Rhs a)
qRhs (SimpleRhs p e ds) = SimpleRhs p <$> qExpr e           <*> mapM qDecl ds
qRhs (GuardedRhs es ds) = GuardedRhs  <$> mapM qCondExpr es <*> mapM qDecl ds

qCondExpr :: Qual (CondExpr a)
qCondExpr (CondExpr p g e) = CondExpr p <$> qExpr g <*> qExpr e

qExpr :: Qual (Expression a)
qExpr l@(Literal           _ _) = return l
qExpr (Variable            a v) = Variable     a <$> qIdent v
qExpr (Constructor         a c) = Constructor  a <$> qIdent c
qExpr (Paren                 e) = Paren          <$> qExpr e
qExpr (Typed             e qty) = Typed          <$> qExpr e
                                                 <*> qQualTypeExpr qty
qExpr (Record           a c fs) =
  Record a <$> qIdent c <*> mapM (qField qExpr) fs
qExpr (RecordUpdate       e fs) = RecordUpdate   <$> qExpr e
                                                 <*> mapM (qField qExpr) fs
qExpr (Tuple                es) = Tuple          <$> mapM qExpr es
qExpr (List               a es) = List a         <$> mapM qExpr es
qExpr (ListCompr          e qs) = ListCompr      <$> qExpr e <*> mapM qStmt qs
qExpr (EnumFrom              e) = EnumFrom       <$> qExpr e
qExpr (EnumFromThen      e1 e2) = EnumFromThen   <$> qExpr e1 <*> qExpr e2
qExpr (EnumFromTo        e1 e2) = EnumFromTo     <$> qExpr e1 <*> qExpr e2
qExpr (EnumFromThenTo e1 e2 e3) = EnumFromThenTo <$> qExpr e1 <*> qExpr e2
                                                              <*> qExpr e3
qExpr (UnaryMinus            e) = UnaryMinus     <$> qExpr e
qExpr (Apply             e1 e2) = Apply          <$> qExpr e1 <*> qExpr e2
qExpr (InfixApply     e1 op e2) = InfixApply     <$> qExpr e1 <*> qInfixOp op
                                                              <*> qExpr e2
qExpr (LeftSection        e op) = LeftSection  <$> qExpr e <*> qInfixOp op
qExpr (RightSection       op e) = RightSection <$> qInfixOp op <*> qExpr e
qExpr (Lambda             ts e) = Lambda       <$> mapM qPattern ts <*> qExpr e
qExpr (Let                ds e) = Let <$> mapM qDecl ds  <*> qExpr e
qExpr (Do                sts e) = Do  <$> mapM qStmt sts <*> qExpr e
qExpr (IfThenElse     e1 e2 e3) = IfThenElse <$> qExpr e1 <*> qExpr e2
                                                          <*> qExpr e3
qExpr (Case            ct e as) = Case ct    <$> qExpr e <*> mapM qAlt as

qStmt :: Qual (Statement a)
qStmt (StmtExpr   e) = StmtExpr <$> qExpr e
qStmt (StmtBind t e) = StmtBind <$> qPattern t <*> qExpr e
qStmt (StmtDecl  ds) = StmtDecl <$> mapM qDecl ds

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
