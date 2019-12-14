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
import Curry.Base.SpanInfo
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
  qfv m (FunctionDecl    _ _ _ eqs) = qfv m eqs
  qfv m (PatternDecl       _ _ rhs) = qfv m rhs
  qfv m (ClassDecl    _ _ _ _ _ ds) = qfv m ds
  qfv m (InstanceDecl _ _ _ _ _ ds) = qfv m ds
  qfv _ _                           = []

instance QuantExpr (Decl a) where
  bv (TypeSig         _ vs _) = vs
  bv (FunctionDecl   _ _ f _) = [f]
  bv (ExternalDecl      _ vs) = bv vs
  bv (PatternDecl      _ t _) = bv t
  bv (FreeDecl          _ vs) = bv vs
  bv (ClassDecl _ _ _ _ _ ds) = concatMap methods ds
  bv _                        = []

instance QualExpr (Equation a) where
  qfv m (Equation _ lhs rhs) = filterBv lhs $ qfv m lhs ++ qfv m rhs

instance QuantExpr (Lhs a) where
  bv = bv . snd . flatLhs

instance QualExpr (Lhs a) where
  qfv m lhs = qfv m $ snd $ flatLhs lhs

instance QualExpr (Rhs a) where
  qfv m (SimpleRhs _ _ e ds) = filterBv ds $ qfv m e  ++ qfv m ds
  qfv m (GuardedRhs _ _ es ds) = filterBv ds $ qfv m es ++ qfv m ds

instance QualExpr (CondExpr a) where
  qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

instance QualExpr (Expression a) where
  qfv _ (Literal             _ _ _) = []
  qfv m (Variable            _ _ v) = maybe [] return $ localIdent m v
  qfv _ (Constructor         _ _ _) = []
  qfv m (Paren               _   e) = qfv m e
  qfv m (Typed               _ e _) = qfv m e
  qfv m (Record           _ _ _ fs) = qfv m fs
  qfv m (RecordUpdate       _ e fs) = qfv m e ++ qfv m fs
  qfv m (Tuple                _ es) = qfv m es
  qfv m (List               _ _ es) = qfv m es
  qfv m (ListCompr          _ e qs) = foldr (qfvStmt m) (qfv m e) qs
  qfv m (EnumFrom              _ e) = qfv m e
  qfv m (EnumFromThen      _ e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (EnumFromTo        _ e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (EnumFromThenTo _ e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
  qfv m (UnaryMinus            _ e) = qfv m e
  qfv m (Apply             _ e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (InfixApply     _ e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
  qfv m (LeftSection        _ e op) = qfv m op ++ qfv m e
  qfv m (RightSection       _ op e) = qfv m op ++ qfv m e
  qfv m (Lambda             _ ts e) = filterBv ts $ qfv m e
  qfv m (Let              _ _ ds e) = filterBv ds $ qfv m ds ++ qfv m e
  qfv m (Do              _ _ sts e) = foldr (qfvStmt m) (qfv m e) sts
  qfv m (IfThenElse     _ e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
  qfv m (Case         _ _ _ e alts) = qfv m e ++ qfv m alts

qfvStmt :: ModuleIdent -> (Statement a) -> [Ident] -> [Ident]
qfvStmt m st fvs = qfv m st ++ filterBv st fvs

instance QualExpr (Statement a) where
  qfv m (StmtExpr   _ e)  = qfv m e
  qfv m (StmtDecl _ _ ds) = filterBv ds $ qfv m ds
  qfv m (StmtBind _ _ e)  = qfv m e

instance QualExpr (Alt a) where
  qfv m (Alt _ t rhs) = filterBv t $ qfv m rhs

instance QuantExpr (Var a) where
  bv (Var _ v) = [v]

instance QuantExpr a => QuantExpr (Field a) where
  bv (Field _ _ t) = bv t

instance QualExpr a => QualExpr (Field a) where
  qfv m (Field _ _ t) = qfv m t

instance QuantExpr (Statement a) where
  bv (StmtExpr   _ _)  = []
  bv (StmtBind _ t _)  = bv t
  bv (StmtDecl _ _ ds) = bv ds

instance QualExpr (InfixOp a) where
  qfv m (InfixOp     a op) = qfv m $ Variable NoSpanInfo a op
  qfv _ (InfixConstr _ _ ) = []

instance QuantExpr (Pattern a) where
  bv (LiteralPattern         _ _ _) = []
  bv (NegativePattern        _ _ _) = []
  bv (VariablePattern        _ _ v) = [v]
  bv (ConstructorPattern  _ _ _ ts) = bv ts
  bv (InfixPattern     _ _ t1 _ t2) = bv t1 ++ bv t2
  bv (ParenPattern             _ t) = bv t
  bv (RecordPattern       _ _ _ fs) = bv fs
  bv (TuplePattern           _  ts) = bv ts
  bv (ListPattern          _  _ ts) = bv ts
  bv (AsPattern              _ v t) = v : bv t
  bv (LazyPattern              _ t) = bv t
  bv (FunctionPattern     _ _ _ ts) = nub $ bv ts
  bv (InfixFuncPattern _ _ t1 _ t2) = nub $ bv t1 ++ bv t2

instance QualExpr (Pattern a) where
  qfv _ (LiteralPattern          _ _ _) = []
  qfv _ (NegativePattern         _ _ _) = []
  qfv _ (VariablePattern         _ _ _) = []
  qfv m (ConstructorPattern   _ _ _ ts) = qfv m ts
  qfv m (InfixPattern      _ _ t1 _ t2) = qfv m [t1, t2]
  qfv m (ParenPattern              _ t) = qfv m t
  qfv m (RecordPattern        _ _ _ fs) = qfv m fs
  qfv m (TuplePattern             _ ts) = qfv m ts
  qfv m (ListPattern            _ _ ts) = qfv m ts
  qfv m (AsPattern              _ _ ts) = qfv m ts
  qfv m (LazyPattern               _ t) = qfv m t
  qfv m (FunctionPattern      _ _ f ts)
    = maybe [] return (localIdent m f) ++ qfv m ts
  qfv m (InfixFuncPattern _ _ t1 op t2)
    = maybe [] return (localIdent m op) ++ qfv m [t1, t2]

instance Expr Constraint where
  fv (Constraint _ _ ty) = fv ty

instance QuantExpr Constraint where
  bv _ = []

instance Expr TypeExpr where
  fv (ConstructorType     _ _) = []
  fv (ApplyType     _ ty1 ty2) = fv ty1 ++ fv ty2
  fv (VariableType       _ tv) = [tv]
  fv (TupleType         _ tys) = fv tys
  fv (ListType          _  ty) = fv ty
  fv (ArrowType     _ ty1 ty2) = fv ty1 ++ fv ty2
  fv (ParenType          _ ty) = fv ty
  fv (ContextType      _ _ ty) = fv ty
  fv (ForallType      _ vs ty) = filter (`notElem` vs) $ fv ty

instance QuantExpr TypeExpr where
  bv (ConstructorType     _ _) = []
  bv (ApplyType     _ ty1 ty2) = bv ty1 ++ bv ty2
  bv (VariableType        _ _) = []
  bv (TupleType         _ tys) = bv tys
  bv (ListType           _ ty) = bv ty
  bv (ArrowType     _ ty1 ty2) = bv ty1 ++ bv ty2
  bv (ParenType          _ ty) = bv ty
  bv (ContextType      _ _ ty) = bv ty
  bv (ForallType     _ tvs ty) = tvs ++ bv ty

filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
filterBv e = filter (`Set.notMember` Set.fromList (bv e))
