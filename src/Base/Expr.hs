{- |
    Module      :  $Header$
    Description :  Extraction of free and bound variables
    Copyright   :  (c)             Wolfgang Lux
                       2011 - 2015 Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler needs to compute the lists of free and bound variables for
    various different entities. We will devote three type classes to that
    purpose. The 'QualExpr' class is expected to take into account
    that it is possible to use a qualified name to refer to a function
    defined in the current module and therefore @M.x@ and @x@, where
    @M@ is the current module name, should be considered the same name.
    However, note that this is correct only after renaming all local
    definitions as @M.x@ always denotes an entity defined at the
    top-level.
-}
module Base.Expr (Expr (..), QualExpr (..), QuantExpr (..)) where

import           Data.List        (nub)
import qualified Data.Set  as Set (fromList, notMember)

import Curry.Base.Ident
import Curry.Syntax

class Expr e where
  -- |Free variables in an 'Expr'
  fv :: e -> [Ident]

class QualExpr e where
  -- |Free qualified variables in an 'Expr'
  qfv :: ModuleIdent -> e -> [Ident]

class QuantExpr e where
  -- |Bounded variables in an 'Expr'
  bv :: e -> [Ident]

instance Expr e => Expr [e] where
  fv = concatMap fv

instance QualExpr e => QualExpr [e] where
  qfv m = concatMap (qfv m)

instance QuantExpr e => QuantExpr [e] where
  bv = concatMap bv

-- The 'Decl' instance of 'QualExpr' returns all free
-- variables on the right hand side, regardless of whether they are bound
-- on the left hand side. This is more convenient as declarations are
-- usually processed in a declaration group where the set of free
-- variables cannot be computed independently for each declaration.

instance QualExpr (Decl a) where
  qfv m (FunctionDecl  _ _ _ eqs) = qfv m eqs
  qfv m (PatternDecl     _ _ rhs) = qfv m rhs
  qfv m (ClassDecl    _ _ _ _ ds) = qfv m ds
  qfv m (InstanceDecl _ _ _ _ ds) = qfv m ds
  qfv _ _                         = []

instance QuantExpr (Decl a) where
  bv (TypeSig          _ vs _) = vs
  bv (FunctionDecl    _ _ f _) = [f]
  bv (ExternalDecl       _ vs) = bv vs
  bv (PatternDecl       _ t _) = bv t
  bv (FreeDecl           _ vs) = bv vs
  bv (ClassDecl    _ _ _ _ ds) = concatMap methods ds
  bv _                         = []

instance QualExpr (Equation a) where
  qfv m (Equation _ lhs rhs) = filterBv lhs $ qfv m lhs ++ qfv m rhs

instance QuantExpr (Lhs a) where
  bv = bv . snd . flatLhs

instance QualExpr (Lhs a) where
  qfv m lhs = qfv m $ snd $ flatLhs lhs

instance QualExpr (Rhs a) where
  qfv m (SimpleRhs _ e ds) = filterBv ds $ qfv m e  ++ qfv m ds
  qfv m (GuardedRhs es ds) = filterBv ds $ qfv m es ++ qfv m ds

instance QualExpr (CondExpr a) where
  qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

instance QualExpr (Expression a) where
  qfv _ (Literal             _ _) = []
  qfv m (Variable            _ v) = maybe [] return $ localIdent m v
  qfv _ (Constructor         _ _) = []
  qfv m (Paren                 e) = qfv m e
  qfv m (Typed               e _) = qfv m e
  qfv m (Record           _ _ fs) = qfv m fs
  qfv m (RecordUpdate       e fs) = qfv m e ++ qfv m fs
  qfv m (Tuple                es) = qfv m es
  qfv m (List               _ es) = qfv m es
  qfv m (ListCompr          e qs) = foldr (qfvStmt m) (qfv m e) qs
  qfv m (EnumFrom              e) = qfv m e
  qfv m (EnumFromThen      e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (EnumFromTo        e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (EnumFromThenTo e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
  qfv m (UnaryMinus            e) = qfv m e
  qfv m (Apply             e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (InfixApply     e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
  qfv m (LeftSection        e op) = qfv m op ++ qfv m e
  qfv m (RightSection       op e) = qfv m op ++ qfv m e
  qfv m (Lambda             ts e) = filterBv ts $ qfv m e
  qfv m (Let                ds e) = filterBv ds $ qfv m ds ++ qfv m e
  qfv m (Do                sts e) = foldr (qfvStmt m) (qfv m e) sts
  qfv m (IfThenElse     e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
  qfv m (Case           _ e alts) = qfv m e ++ qfv m alts

qfvStmt :: ModuleIdent -> (Statement a) -> [Ident] -> [Ident]
qfvStmt m st fvs = qfv m st ++ filterBv st fvs

instance QualExpr (Statement a) where
  qfv m (StmtExpr   e) = qfv m e
  qfv m (StmtDecl  ds) = filterBv ds $ qfv m ds
  qfv m (StmtBind _ e) = qfv m e

instance QualExpr (Alt a) where
  qfv m (Alt _ t rhs) = filterBv t $ qfv m rhs

instance QuantExpr (Var a) where
  bv (Var _ v) = [v]

instance QuantExpr a => QuantExpr (Field a) where
  bv (Field _ _ t) = bv t

instance QualExpr a => QualExpr (Field a) where
  qfv m (Field _ _ t) = qfv m t

instance QuantExpr (Statement a) where
  bv (StmtExpr   _) = []
  bv (StmtBind t _) = bv t
  bv (StmtDecl  ds) = bv ds

instance QualExpr (InfixOp a) where
  qfv m (InfixOp     a op) = qfv m $ Variable a op
  qfv _ (InfixConstr _ _ ) = []

instance QuantExpr (Pattern a) where
  bv (LiteralPattern         _ _) = []
  bv (NegativePattern        _ _) = []
  bv (VariablePattern        _ v) = [v]
  bv (ConstructorPattern  _ _ ts) = bv ts
  bv (InfixPattern     _ t1 _ t2) = bv t1 ++ bv t2
  bv (ParenPattern             t) = bv t
  bv (RecordPattern       _ _ fs) = bv fs
  bv (TuplePattern            ts) = bv ts
  bv (ListPattern           _ ts) = bv ts
  bv (AsPattern              v t) = v : bv t
  bv (LazyPattern              t) = bv t
  bv (FunctionPattern     _ _ ts) = nub $ bv ts
  bv (InfixFuncPattern _ t1 _ t2) = nub $ bv t1 ++ bv t2

instance QualExpr (Pattern a) where
  qfv _ (LiteralPattern          _ _) = []
  qfv _ (NegativePattern         _ _) = []
  qfv _ (VariablePattern         _ _) = []
  qfv m (ConstructorPattern   _ _ ts) = qfv m ts
  qfv m (InfixPattern      _ t1 _ t2) = qfv m [t1, t2]
  qfv m (ParenPattern              t) = qfv m t
  qfv m (RecordPattern        _ _ fs) = qfv m fs
  qfv m (TuplePattern             ts) = qfv m ts
  qfv m (ListPattern            _ ts) = qfv m ts
  qfv m (AsPattern              _ ts) = qfv m ts
  qfv m (LazyPattern               t) = qfv m t
  qfv m (FunctionPattern      _ f ts)
    = maybe [] return (localIdent m f) ++ qfv m ts
  qfv m (InfixFuncPattern _ t1 op t2)
    = maybe [] return (localIdent m op) ++ qfv m [t1, t2]

instance Expr Constraint where
  fv (Constraint _ ty) = fv ty

instance QuantExpr Constraint where
  bv _ = []

instance Expr QualTypeExpr where
  fv (QualTypeExpr _ ty) = fv ty

instance QuantExpr QualTypeExpr where
  bv (QualTypeExpr _ ty) = bv ty

instance Expr TypeExpr where
  fv (ConstructorType     _) = []
  fv (ApplyType     ty1 ty2) = fv ty1 ++ fv ty2
  fv (VariableType       tv) = [tv]
  fv (TupleType         tys) = fv tys
  fv (ListType           ty) = fv ty
  fv (ArrowType     ty1 ty2) = fv ty1 ++ fv ty2
  fv (ParenType          ty) = fv ty
  fv (ForallType      vs ty) = filter (`notElem` vs) $ fv ty

instance QuantExpr TypeExpr where
  bv (ConstructorType     _) = []
  bv (ApplyType     ty1 ty2) = bv ty1 ++ bv ty2
  bv (VariableType        _) = []
  bv (TupleType         tys) = bv tys
  bv (ListType           ty) = bv ty
  bv (ArrowType     ty1 ty2) = bv ty1 ++ bv ty2
  bv (ParenType          ty) = bv ty
  bv (ForallType     tvs ty) = tvs ++ bv ty

filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
filterBv e = filter (`Set.notMember` Set.fromList (bv e))
