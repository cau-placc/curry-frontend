{- |
    Module      :  $Header$
    Description :  Extraction of free qualified annotated variables
    Copyright   :  (c) 2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    TODO
-}
module Base.AnnotExpr (QualAnnotExpr (..)) where

import qualified Data.Set  as Set (fromList, notMember)

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax

import Base.Expr
import Base.Types
import Base.Typing

class QualAnnotExpr e where
  -- |Free qualified annotated variables in an 'Expr'
  qafv :: ModuleIdent -> e Type -> [(Type, Ident)]

-- The 'Decl' instance of 'QualAnnotExpr' returns all free
-- variables on the right hand side, regardless of whether they are bound
-- on the left hand side. This is more convenient as declarations are
-- usually processed in a declaration group where the set of free
-- variables cannot be computed independently for each declaration.

instance QualAnnotExpr Decl where
  qafv m (FunctionDecl    _ _ _ eqs) = concatMap (qafv m) eqs
  qafv m (PatternDecl       _ _ rhs) = qafv m rhs
  qafv m (ClassDecl    _ _ _ _ _ ds) = concatMap (qafv m) ds
  qafv m (InstanceDecl _ _ _ _ _ ds) = concatMap (qafv m) ds
  qafv _ _                           = []

instance QualAnnotExpr Equation where
  qafv m (Equation _ lhs rhs) = filterBv lhs $ qafv m lhs ++ qafv m rhs

instance QualAnnotExpr Lhs where
  qafv m = concatMap (qafv m) . snd . flatLhs

instance QualAnnotExpr Rhs where
  qafv m (SimpleRhs _ _ e ds) = filterBv ds $ qafv m e ++ concatMap (qafv m) ds
  qafv m (GuardedRhs _ _ es ds) =
    filterBv ds $ concatMap (qafv m) es ++ concatMap (qafv m) ds

instance QualAnnotExpr CondExpr where
  qafv m (CondExpr _ g e) = qafv m g ++ qafv m e

instance QualAnnotExpr Expression where
  qafv _ (Literal             _ _ _) = []
  qafv m (Variable           _ ty v) =
    maybe [] (return . (\v' -> (ty, v'))) $ localIdent m v
  qafv _ (Constructor         _ _ _) = []
  qafv m (Paren                 _ e) = qafv m e
  qafv m (Typed               _ e _) = qafv m e
  qafv m (Record           _ _ _ fs) = concatMap (qafvField m) fs
  qafv m (RecordUpdate       _ e fs) = qafv m e ++ concatMap (qafvField m) fs
  qafv m (Tuple                _ es) = concatMap (qafv m) es
  qafv m (List               _ _ es) = concatMap (qafv m) es
  qafv m (ListCompr          _ e qs) = foldr (qafvStmt m) (qafv m e) qs
  qafv m (EnumFrom              _ e) = qafv m e
  qafv m (EnumFromThen      _ e1 e2) = qafv m e1 ++ qafv m e2
  qafv m (EnumFromTo        _ e1 e2) = qafv m e1 ++ qafv m e2
  qafv m (EnumFromThenTo _ e1 e2 e3) = qafv m e1 ++ qafv m e2 ++ qafv m e3
  qafv m (UnaryMinus            _ e) = qafv m e
  qafv m (Apply             _ e1 e2) = qafv m e1 ++ qafv m e2
  qafv m (InfixApply     _ e1 op e2) = qafv m op ++ qafv m e1 ++ qafv m e2
  qafv m (LeftSection        _ e op) = qafv m op ++ qafv m e
  qafv m (RightSection       _ op e) = qafv m op ++ qafv m e
  qafv m (Lambda             _ ts e) = filterBv ts $ qafv m e
  qafv m (Let              _ _ ds e) =
    filterBv ds $ concatMap (qafv m) ds ++ qafv m e
  qafv m (Do              _ _ sts e) = foldr (qafvStmt m) (qafv m e) sts
  qafv m (IfThenElse     _ e1 e2 e3) = qafv m e1 ++ qafv m e2 ++ qafv m e3
  qafv m (Case         _ _ _ e alts) = qafv m e ++ concatMap (qafv m) alts

qafvField :: QualAnnotExpr e => ModuleIdent -> Field (e Type) -> [(Type, Ident)]
qafvField m (Field _ _ t) = qafv m t

qafvStmt :: ModuleIdent -> Statement Type -> [(Type, Ident)] -> [(Type, Ident)]
qafvStmt m st fvs = qafv m st ++ filterBv st fvs

instance QualAnnotExpr Statement where
  qafv m (StmtExpr   _  e) = qafv m e
  qafv m (StmtDecl _ _ ds) = filterBv ds $ concatMap (qafv m) ds
  qafv m (StmtBind _ _  e) = qafv m e

instance QualAnnotExpr Alt where
  qafv m (Alt _ t rhs) = filterBv t $ qafv m rhs

instance QualAnnotExpr InfixOp where
  qafv m (InfixOp    ty op) = qafv m $ Variable NoSpanInfo ty op
  qafv _ (InfixConstr _ _ ) = []

instance QualAnnotExpr Pattern where
  qafv _ (LiteralPattern           _ _ _) = []
  qafv _ (NegativePattern          _ _ _) = []
  qafv _ (VariablePattern          _ _ _) = []
  qafv m (ConstructorPattern    _ _ _ ts) = concatMap (qafv m) ts
  qafv m (InfixPattern       _ _ t1 _ t2) = qafv m t1 ++ qafv m t2
  qafv m (ParenPattern               _ t) = qafv m t
  qafv m (RecordPattern         _ _ _ fs) = concatMap (qafvField m) fs
  qafv m (TuplePattern              _ ts) = concatMap (qafv m) ts
  qafv m (ListPattern             _ _ ts) = concatMap (qafv m) ts
  qafv m (AsPattern                _ _ t) = qafv m t
  qafv m (LazyPattern                _ t) = qafv m t
  qafv m (FunctionPattern      _ ty f ts) =
    maybe [] (return . (\f' -> (ty', f'))) (localIdent m f) ++
      concatMap (qafv m) ts
    where ty' = foldr TypeArrow ty $ map typeOf ts
  qafv m (InfixFuncPattern _ ty t1 op t2) =
    maybe [] (return . (\op' -> (ty', op'))) (localIdent m op) ++
      concatMap (qafv m) [t1, t2]
    where ty' = foldr TypeArrow ty $ map typeOf [t1, t2]

filterBv :: QuantExpr e => e -> [(Type, Ident)] -> [(Type, Ident)]
filterBv e = filter ((`Set.notMember` Set.fromList (bv e)) . snd)
