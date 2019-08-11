module Base.Linearity (isLinearIdt) where

import Control.Monad.State
import Data.Foldable
import Data.List
import Data.Maybe
import qualified Data.Set as Set

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Syntax
import Base.Types
import Base.Expr

isLinearIdt :: ModuleIdent -> [Decl PredType] -> QualIdent -> Bool
isLinearIdt mid ds qid =
  isJust $ evalStateT (linearityAnalysis qid []) initState
  where initState = LinearityState mid Set.empty ds

data LinearityState = LinearityState
  { moduleIdent :: ModuleIdent
  , linearInfo  :: Set.Set QualIdent
  , allDecls    :: [Decl PredType]
  }

type LSM a = StateT LinearityState Maybe a

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

mFail :: StateT LinearityState Maybe a
mFail = fail ""

class Linear a where
  linearityAnalysis :: a -> [Ident] -> LSM [Ident]

instance Linear QualIdent where
  linearityAnalysis qid xs = do
    cmid <- getModuleIdent
    case qidModule qid of
      Just mid | mid == cmid -> do md <- getDeclM (qidIdent qid)
                                   case md of
                                     Just d  -> linearityAnalysis d xs
                                     Nothing -> return xs -- something local, will be checked somewhere else
               | otherwise   -> mFail -- other module
      _ -> return xs

instance Linear (Decl a) where
  linearityAnalysis (FunctionDecl _ _ idt eqs) xs = do
    mid <- getModuleIdent
    let qid = qualifyWith mid idt
    lin <- lookupLinearity qid
    if lin
      then return xs
      else do setLinearity qid -- assume linearity to handle recursive dependencies
              mapM_ (`linearityAnalysis` xs) eqs
              return xs
  linearityAnalysis (PatternDecl _ p rhs) xs = linearityAnalysis p xs >> linearityAnalysis rhs xs
  linearityAnalysis (FreeDecl _ _       ) xs = return xs
  linearityAnalysis _                     _  = mFail

instance Linear (Equation a) where
  linearityAnalysis (Equation _ lhs rhs) xs = linearityAnalysis lhs xs >> linearityAnalysis rhs xs

instance Linear (Lhs a) where
  linearityAnalysis lhs xs = foldrM linearityAnalysis xs ps
    where
      ps = snd $ flatLhs lhs

instance Linear (Pattern a) where
  linearityAnalysis (VariablePattern _ _ idt    ) xs
                                    | idt `elem`  xs = mFail
                                    | otherwise      = return (idt:xs)
  linearityAnalysis (AsPattern       _   idt p  ) xs
                                    | idt `elem`  xs = mFail
                                    | otherwise      = linearityAnalysis p (idt:xs)
  linearityAnalysis (LiteralPattern  _ _ _      ) xs = return xs
  linearityAnalysis (NegativePattern _ _ _      ) xs = return xs
  linearityAnalysis (ConstructorPattern _ _ _ ps) xs = foldrM linearityAnalysis xs ps
  linearityAnalysis (InfixPattern _ _ p1 _ p2   ) xs = foldrM linearityAnalysis xs [p1, p2]
  linearityAnalysis (ParenPattern _ p           ) xs = linearityAnalysis p xs
  linearityAnalysis (RecordPattern _ _ _ fs     ) xs = foldrM linearityAnalysis xs fs
  linearityAnalysis (TuplePattern  _ ps         ) xs = foldrM linearityAnalysis xs ps
  linearityAnalysis (ListPattern _ _ ps         ) xs = foldrM linearityAnalysis xs ps
  linearityAnalysis (LazyPattern _ p            ) xs = linearityAnalysis p xs
  linearityAnalysis (FunctionPattern _ _ qid ps    ) xs =
    linearityAnalysis qid [] >> foldrM linearityAnalysis xs ps
  linearityAnalysis (InfixFuncPattern _ _ p2 qid p1) xs =
    linearityAnalysis qid [] >> foldrM linearityAnalysis xs [p1, p2]

instance Linear (Rhs a) where
  linearityAnalysis (SimpleRhs  _ e   ds) xs = foldrM localDeclAnalysis xs ds >>= linearityAnalysis e
  linearityAnalysis (GuardedRhs _ ces ds) xs = do
    xs' <- foldrM localDeclAnalysis xs ds
    xss <- mapM (`linearityAnalysis` xs') ces
    return (nub $ concat xss)

instance Linear (CondExpr a) where
  linearityAnalysis (CondExpr _ e1 e2) xs = linearityAnalysis e1 xs >>= linearityAnalysis e2

instance Linear (InfixOp a) where
  linearityAnalysis (InfixOp     _ qid) xs = linearityAnalysis qid xs
  linearityAnalysis (InfixConstr _ _  ) xs = return xs

instance Linear (Expression a) where
  linearityAnalysis (Variable _ _ qid     ) xs
                           | isQualified qid   = linearityAnalysis qid [] >> return xs
                           | idt `elem`     xs = mFail
                           | otherwise         = return (idt:xs)
    where idt = qidIdent qid
  linearityAnalysis (Literal     _ _ _     ) xs = return xs -- we assume fromInt is linear.
  linearityAnalysis (Constructor _ _ _     ) xs = return xs
  linearityAnalysis (Paren _ e             ) xs = linearityAnalysis e xs
  linearityAnalysis (Typed _ e _           ) xs = linearityAnalysis e xs
  linearityAnalysis (UnaryMinus     _ e    ) xs = linearityAnalysis e xs -- we assume negate is linear
  linearityAnalysis (Apply _ e1 e2         ) xs = linearityAnalysis e1 xs >>= linearityAnalysis e2
  linearityAnalysis (ListCompr _ e st      ) xs = foldrM linearityAnalysis xs st >>= linearityAnalysis e
  linearityAnalysis (Do _ st e             ) xs = foldrM linearityAnalysis xs st >>= linearityAnalysis e
  linearityAnalysis (Let _ ds e            ) xs = foldrM localDeclAnalysis xs ds >>= linearityAnalysis e
  linearityAnalysis (RecordUpdate _ e fs   ) xs = foldrM linearityAnalysis xs fs >>= linearityAnalysis e
  linearityAnalysis (Record _ _ _ fs       ) xs = foldrM linearityAnalysis xs fs
  linearityAnalysis (Tuple _ es            ) xs = foldrM linearityAnalysis xs es
  linearityAnalysis (List _ _ es           ) xs = foldrM linearityAnalysis xs es
  linearityAnalysis (EnumFrom       _ _    ) _  = mFail -- Typeclass used
  linearityAnalysis (EnumFromThen   _ _ _  ) _  = mFail -- Typeclass used
  linearityAnalysis (EnumFromTo     _ _   _) _  = mFail -- Typeclass used
  linearityAnalysis (EnumFromThenTo _ _ _ _) _  = mFail -- Typeclass used
  linearityAnalysis (Lambda _ ps e         ) xs = patRhsAnalysis xs ps (simpleRhs NoSpanInfo e)
  linearityAnalysis (Case _ _ e as         ) xs = altsAnalysis as xs >>= linearityAnalysis e
  linearityAnalysis (IfThenElse _ e1 e2 e3 ) xs = do
    xs1  <- linearityAnalysis e1 xs
    xs2a <- linearityAnalysis e2 xs1
    xs2b <- linearityAnalysis e3 xs1
    return (nub $ xs2a ++ xs2b)
  linearityAnalysis (InfixApply _ e1 op e2 ) xs = linearityAnalysis op [] >> foldrM linearityAnalysis xs [e1, e2]
  linearityAnalysis (LeftSection  _ e op   ) xs = linearityAnalysis op [] >> linearityAnalysis e xs
  linearityAnalysis (RightSection _ op e   ) xs = linearityAnalysis op [] >> linearityAnalysis e xs

instance Linear (Statement a) where
  linearityAnalysis (StmtExpr _   e) xs = linearityAnalysis e xs
  linearityAnalysis (StmtDecl _ ds ) xs = foldrM localDeclAnalysis xs ds
  linearityAnalysis (StmtBind _ p e) xs = patRhsAnalysis xs [p] (simpleRhs NoSpanInfo e)

instance Linear a => Linear (Field a) where
  linearityAnalysis (Field _ _ a) = linearityAnalysis a

localDeclAnalysis :: Decl a -> [Ident] -> LSM [Ident]
localDeclAnalysis (FunctionDecl _ _ _ eqs) xs =
  nub . concat <$> mapM (`linearityAnalysis` xs) eqs
localDeclAnalysis (PatternDecl _ p rhs   ) xs = linearityAnalysis p xs >>= linearityAnalysis rhs
localDeclAnalysis (FreeDecl _ _          ) xs = return xs
localDeclAnalysis _                        _  = mFail

altsAnalysis :: [Alt a] -> [Ident] -> LSM [Ident]
altsAnalysis as xs = do
  xss <- mapM (`altAnalysis` xs) as
  return (nub $ concat xss)
  where
    altAnalysis (Alt _ p rhs) xs' = patRhsAnalysis xs' [p] rhs

patRhsAnalysis :: [Ident] -> [Pattern a] -> Rhs a
               -> LSM [Ident]
patRhsAnalysis xs ps rhs = do
  m <- getModuleIdent
  let lfv = filterBv ps $ qfv m ps ++ qfv m rhs
  let sfv = Set.fromList lfv
  let sxs = Set.fromList xs
  mapM_ (`linearityAnalysis` []) ps
  _ <- linearityAnalysis rhs []
  if Set.disjoint sfv sxs
    then return (lfv ++ xs)
    else mFail

filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
filterBv e = filter (`Set.notMember` Set.fromList (bv e))

{- HLINT ignore "Use record patterns" -}
