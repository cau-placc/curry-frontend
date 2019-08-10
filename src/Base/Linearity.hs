module Base.Linearity (isLinearIdt) where

import Control.Monad.State
import Control.Monad.Extra
import Data.Foldable
import Data.List
import qualified Data.Set as Set

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax
import Base.Types
import Base.Expr

isLinearIdt :: ModuleIdent -> [Decl PredType] -> QualIdent -> Bool
isLinearIdt mid ds qid =
  evalState (linearityAnalysis qid) initState
  where initState = LinearityState mid Set.empty ds

data LinearityState = LinearityState
  { moduleIdent :: ModuleIdent
  , linearInfo  :: Set.Set QualIdent
  , allDecls    :: [Decl PredType]
  }

type LSM a = State LinearityState a

getModuleIdent :: LSM ModuleIdent
getModuleIdent = gets moduleIdent

lookupLinearity :: QualIdent -> LSM Bool
lookupLinearity qid = do
  li <- gets linearInfo
  return $ Set.member qid li

setLinearity :: QualIdent -> LSM ()
setLinearity qid = do
  s <- get
  let li = Set.insert qid $ linearInfo s
  let s' = s { linearInfo = li }
  put s'

getDeclM :: Ident -> LSM (Maybe (Decl PredType))
getDeclM idt = getDecl idt <$> gets allDecls

getDecl :: Ident -> [Decl a] -> Maybe (Decl a)
getDecl idt ds =
  case filter isCorrect ds of
    [x] -> Just x
    _   -> Nothing
  where
    isCorrect (FunctionDecl _ _ fid _) = fid == idt
    isCorrect (ExternalDecl _ vs)      = any isCorrectVar vs
    isCorrect _                        = False

    isCorrectVar (Var _ fid) = fid == idt

class Linear a where
  linearityAnalysis :: a -> LSM Bool

instance Linear a => Linear [a] where
  linearityAnalysis = fmap and . mapM linearityAnalysis

instance Linear QualIdent where
  linearityAnalysis qid = do
    cmid <- getModuleIdent
    case qidModule qid of
      Just mid | mid == cmid -> do md <- getDeclM (qidIdent qid)
                                   case md of
                                     Just d  -> linearityAnalysis d
                                     Nothing -> return True -- something local, will be checked somewhere else
               | otherwise   -> return False -- other module
      _ -> return True -- not a function

instance Linear (Decl a) where
  linearityAnalysis (FunctionDecl _ _ idt eqs) = do
    mid <- getModuleIdent
    let qid = qualifyWith mid idt
    lin <- lookupLinearity qid
    if lin
      then return True
      else setLinearity qid -- assume linearity to handle recursive dependencies
           >> linearityAnalysis eqs
  linearityAnalysis (PatternDecl _ p rhs) = do
    linP <- snd <$> patternAnalysis p ([], True)
    linR <- linearityAnalysis rhs
    return (linP && linR)
  linearityAnalysis (FreeDecl _ _) = return True
  linearityAnalysis d              = return False

instance Linear (Equation a) where
  linearityAnalysis (Equation _ lhs rhs) = (&&)
    <$> linearityAnalysis lhs
    <*> linearityAnalysis rhs

instance Linear (Lhs a) where
  linearityAnalysis lhs = snd <$> foldrM patternAnalysis ([], True) ps
    where
      ps = snd $ flatLhs lhs

instance Linear (Pattern a) where
  linearityAnalysis p = snd <$> patternAnalysis p ([], True)

instance Linear (Rhs a) where
  linearityAnalysis (SimpleRhs _ e []      ) = linearityAnalysis e
  linearityAnalysis (SimpleRhs _ e ds@(_:_)) = return False -- TODO
  linearityAnalysis (GuardedRhs _ ces [])       = linearityAnalysis ces
  linearityAnalysis (GuardedRhs _ ces ds@(_:_)) = return False -- TODO

instance Linear (Expression a) where
  linearityAnalysis e = snd <$> exprAnalysis e ([], True)

instance Linear (CondExpr a) where
  linearityAnalysis (CondExpr _ e1 e2) = do
    xs <- exprAnalysis e1 ([], True)
    snd <$> exprAnalysis e2 xs

instance Linear (InfixOp a) where
  linearityAnalysis (InfixOp     _ qid) = linearityAnalysis qid
  linearityAnalysis (InfixConstr _ _  ) = return True

-- TODO: use Maybe [Ident] instead of ([Ident], Bool),
-- as there is no way to recover from a false

exprAnalysis :: Expression a -> ([Ident], Bool) -> LSM ([Ident], Bool)
exprAnalysis _                  (_, False) = return ([], False)
exprAnalysis (Variable _ _ qid) (xs, _   )
                         | isQualified qid = (,) xs <$> linearityAnalysis qid
                         | otherwise       = return (idt:xs, idt `elem` xs)
  where idt = qidIdent qid
exprAnalysis (Literal     _ _ _     ) xs = return xs
exprAnalysis (Constructor _ _ _     ) xs = return xs
exprAnalysis (Paren _ e             ) xs = exprAnalysis e xs
exprAnalysis (Typed _ e _           ) xs = exprAnalysis e xs
exprAnalysis (UnaryMinus     _ e    ) xs = exprAnalysis e xs
exprAnalysis (Apply _ e1 e2         ) xs = exprAnalysis e1 xs >>= exprAnalysis e2
exprAnalysis (IfThenElse _ e1 e2 e3 ) xs = exprAnalysis e1 xs >>= exprAnalysis e2 >>= exprAnalysis e3
exprAnalysis (ListCompr _ e st      ) xs = foldrM stmtAnalysis xs st >>= exprAnalysis e
exprAnalysis (Do _ st e             ) xs = foldrM stmtAnalysis xs st >>= exprAnalysis e
exprAnalysis (RecordUpdate _ e fs   ) xs = foldrM (fieldAnalysis exprAnalysis) xs fs >>= exprAnalysis e
exprAnalysis (Record _ _ _ fs       ) xs = foldrM (fieldAnalysis exprAnalysis) xs fs
exprAnalysis (Tuple _ es            ) xs = foldrM exprAnalysis xs es
exprAnalysis (List _ _ es           ) xs = foldrM exprAnalysis xs es
exprAnalysis (EnumFrom       _ _    ) xs = return ([], False) -- Typeclass used
exprAnalysis (EnumFromThen   _ _ _  ) xs = return ([], False) -- Typeclass used
exprAnalysis (EnumFromTo     _ _   _) xs = return ([], False) -- Typeclass used
exprAnalysis (EnumFromThenTo _ _ _ _) xs = return ([], False) -- Typeclass used
exprAnalysis (Lambda _ ps e         ) xs = patRhsAnalysis (fst xs) ps (simpleRhs NoSpanInfo e)
exprAnalysis (Case _ _ e as         ) xs = altsAnalysis as xs >>= exprAnalysis e
exprAnalysis (Let _ [] e            ) xs = exprAnalysis e xs
exprAnalysis (Let _ _ _             ) xs = return ([], False) -- TODO
exprAnalysis (InfixApply _ e1 op e2) (xs, _) = do
  lin <- linearityAnalysis op
  foldrM exprAnalysis (xs, lin) [e1, e2]
exprAnalysis (LeftSection  _ e op   ) (xs, _) = do
  lin <- linearityAnalysis op
  exprAnalysis e (xs, lin)
exprAnalysis (RightSection _ op e   ) (xs, _) = do
  lin <- linearityAnalysis op
  exprAnalysis e (xs, lin)

stmtAnalysis :: Statement a -> ([Ident], Bool) -> LSM ([Ident], Bool)
stmtAnalysis _                (_, False) = return ([], False)
stmtAnalysis (StmtExpr _   e) xs = exprAnalysis e xs
stmtAnalysis (StmtDecl _ [] ) xs = return xs
stmtAnalysis (StmtDecl _ _  ) xs = return ([], False) -- TODO
stmtAnalysis (StmtBind _ p e) xs = patRhsAnalysis (fst xs) [p] (simpleRhs NoSpanInfo e)

patternAnalysis :: Pattern a -> ([Ident], Bool) -> LSM ([Ident], Bool)
patternAnalysis _                             (_, False) = return ([], False)
patternAnalysis (VariablePattern _ _ idt    ) (xs, _   ) = return (idt:xs, idt `elem` xs)
patternAnalysis (AsPattern       _   idt p  ) (xs, _   ) = patternAnalysis p (idt:xs, idt `elem` xs)
patternAnalysis (LiteralPattern  _ _ _      ) xs = return xs
patternAnalysis (NegativePattern _ _ _      ) xs = return xs
patternAnalysis (ConstructorPattern _ _ _ ps) xs = foldrM patternAnalysis xs ps
patternAnalysis (InfixPattern _ _ p1 _ p2   ) xs = foldrM patternAnalysis xs [p1, p2]
patternAnalysis (ParenPattern _ p           ) xs = patternAnalysis p xs
patternAnalysis (RecordPattern _ _ _ fs     ) xs = foldrM (fieldAnalysis patternAnalysis) xs fs
patternAnalysis (TuplePattern  _ ps         ) xs = foldrM patternAnalysis xs ps
patternAnalysis (ListPattern _ _ ps         ) xs = foldrM patternAnalysis xs ps
patternAnalysis (LazyPattern _ p            ) xs = patternAnalysis p xs
patternAnalysis (FunctionPattern _ _ qid ps    ) (xs, _) = do
  lin <- linearityAnalysis qid
  foldrM patternAnalysis (xs, lin) ps
patternAnalysis (InfixFuncPattern _ _ p2 qid p1) (xs, _) = do
  lin <- linearityAnalysis qid
  foldrM patternAnalysis (xs, lin) [p1, p2]

altsAnalysis :: [Alt a] -> ([Ident], Bool) -> LSM ([Ident], Bool)
altsAnalysis as (_  , False) = return ([], False)
altsAnalysis as (xs', True ) = do
  (xss, bs) <- unzip <$> mapM (altAnalysis xs') as
  return (nub $ concat xss, and bs)
  where
    altAnalysis xs (Alt _ p rhs) = patRhsAnalysis xs [p] rhs

patRhsAnalysis :: [Ident] -> [Pattern a] -> Rhs a
               -> LSM ([Ident], Bool)
patRhsAnalysis xs ps rhs = do
  m <- getModuleIdent
  let  fv = filterBv ps $ qfv m ps ++ qfv m rhs
  let sfv = Set.fromList fv
  let sxs = Set.fromList xs
  linP <- linearityAnalysis ps
  linR <- linearityAnalysis rhs
  return (fv++xs, linP && linR && Set.disjoint sfv sxs)

fieldAnalysis :: (a -> ([Ident], Bool) -> LSM ([Ident], Bool))
              -> Field a -> ([Ident], Bool) -> LSM ([Ident], Bool)
fieldAnalysis f (Field _ _ a) xs = f a xs

filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
filterBv e = filter (`Set.notMember` Set.fromList (bv e))

{- HLINT ignore "Use record patterns" -}
