{- |
    Module      :  $Header$
    Description :  Checking import specifications
    Copyright   :  (c) 2016       Jan Tikovsky
                       2016       Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  jrt@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the function 'importCheck' to check and expand
    the import specifications of all import declarations.
-}
module Checks.ImportSyntaxCheck(importCheck) where

import           Control.Monad              (liftM, unless)
import qualified Control.Monad.State as S   (State, gets, modify, runState)
import           Data.List                  (nub, union)
import qualified Data.Map            as Map
import           Data.Maybe                 (fromMaybe)

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Base.SpanInfo
import Curry.Syntax hiding (Var (..))

import Base.Messages
import Base.TopEnv

importCheck :: Interface -> Maybe ImportSpec -> (Maybe ImportSpec, [Message])
importCheck (Interface m _ ds o) is = runExpand (expandSpecs is) m' mTCEnv mTyEnv
  where
  m' = maybe id applyOriginPragma o m
  mTCEnv = intfEnv types  ds
  mTyEnv = intfEnv values ds

data ITypeInfo = Data  QualIdent [Ident]
               | Alias QualIdent
               | Class QualIdent [Ident]
 deriving Show

instance Entity ITypeInfo where
  origName (Data  tc  _) = tc
  origName (Alias tc   ) = tc
  origName (Class cls _) = cls

  merge (Data tc1 cs1) (Data tc2 cs2)
    | tc1 == tc2 && (null cs1 || null cs2 || cs1 == cs2) =
        Just $ Data tc1 (if null cs1 then cs2 else cs1)
  merge l@(Alias tc1) (Alias tc2)
    | tc1 == tc2 = Just l
  merge (Class cls1 ms1) (Class cls2 ms2)
    | cls1 == cls2 && (null ms1 || null ms2 || ms1 == ms2) =
        Just $ Class cls1 (if null ms1 then ms2 else ms1)
  merge _ _ = Nothing

data IValueInfo = Constr QualIdent
                | Var    QualIdent [QualIdent]
 deriving Show

instance Entity IValueInfo where
  origName (Constr c) = c
  origName (Var  x _) = x

  merge (Constr c1) (Constr c2)
    | c1 == c2 = Just (Constr c1)
  merge (Var x1 cs1) (Var x2 cs2)
    | x1 == x2 = Just (Var x1 (cs1 `union` cs2))
  merge _ _ = Nothing


intfEnv :: Entity a => (IDecl -> [a]) -> [IDecl] -> IdentMap a
intfEnv idents ds = foldr bindId Map.empty (concatMap idents ds)
  where bindId x = Map.insert (unqualify (origName x)) x

types :: IDecl -> [ITypeInfo]
types (IDataDecl     o _ tc _ _ cs hs) = [Data (maybe id applyOriginPragma o tc) (filter (`notElem` hs) xs)]
  where xs = map constrId cs ++ nub (concatMap recordLabels cs)
types (INewtypeDecl  o _ tc _ _ nc hs) = [Data (maybe id applyOriginPragma o tc) (filter (`notElem` hs) xs)]
  where xs = nconstrId nc : nrecordLabels nc
types (ITypeDecl         o _ tc _ _ _) = [Alias (maybe id applyOriginPragma o tc)]
types (IClassDecl o _ _ cls _ _ ms hs) = [Class (maybe id applyOriginPragma o cls) (filter (`notElem` hs) xs)]
  where xs = map imethod ms
types _                              = []

values :: IDecl -> [IValueInfo]
values (IDataDecl     o _ tc _ _ cs hs) =
  cidents (maybe id applyOriginPragma o tc) (map constrId cs) hs ++
  lidents (maybe id applyOriginPragma o tc) [(l, lconstrs cs l) | l <- nub (concatMap recordLabels cs)] hs
  where lconstrs cons l = [constrId c | c <- cons, l `elem` recordLabels c]
values (INewtypeDecl  o _ tc _ _ nc hs) =
  cidents (maybe id applyOriginPragma o tc) [nconstrId nc] hs ++
  lidents (maybe id applyOriginPragma o tc) [(l, [c]) | NewRecordDecl _ c (l, _) <- [nc]] hs
values (IFunctionDecl      o _ f _ _ _) = [Var (maybe id applyOriginPragma o f) []]
values (IClassDecl o _ _ cls _ _ ms hs) = midents (maybe id applyOriginPragma o cls) (map imethod ms) hs
values _                                = []

cidents :: QualIdent -> [Ident] -> [Ident] -> [IValueInfo]
cidents tc cs hs = [Constr (qualifyLike tc c) | c <- cs, c `notElem` hs]

lidents :: QualIdent -> [(Ident, [Ident])] -> [Ident] -> [IValueInfo]
lidents tc ls hs = [ Var (qualifyLike tc l) (map (qualifyLike tc) cs)
                   | (l, cs) <- ls, l `notElem` hs
                   ]

midents :: QualIdent -> [Ident] -> [Ident] -> [IValueInfo]
midents cls fs hs = [Var (qualifyLike cls f) [] | f <- fs, f `notElem` hs]

-- ---------------------------------------------------------------------------
-- Expansion of the import specification
-- ---------------------------------------------------------------------------

-- After the environments have been initialized, the optional import
-- specifications can be checked. There are two kinds of import
-- specifications, a ``normal'' one, which names the entities that shall
-- be imported, and a hiding specification, which lists those entities
-- that shall not be imported.
--
-- There is a subtle difference between both kinds of
-- specifications: While it is not allowed to list a data constructor
-- outside of its type in a ``normal'' specification, it is allowed to
-- hide a data constructor explicitly. E.g., if module \texttt{A} exports
-- the data type \texttt{T} with constructor \texttt{C}, the data
-- constructor can be imported with one of the two specifications
--
-- import A (T(C))
-- import A (T(..))
--
-- but can be hidden in three different ways:
--
-- import A hiding (C)
-- import A hiding (T (C))
-- import A hiding (T (..))
--
-- The functions \texttt{expandImport} and \texttt{expandHiding} check
-- that all entities in an import specification are actually exported
-- from the module. In addition, all imports of type constructors are
-- changed into a \texttt{T()} specification and explicit imports for the
-- data constructors are added.

type IdentMap    = Map.Map Ident

type ExpTCEnv    = IdentMap ITypeInfo
type ExpValueEnv = IdentMap IValueInfo

data ExpandState = ExpandState
  { expModIdent :: ModuleIdent
  , expTCEnv    :: ExpTCEnv
  , expValueEnv :: ExpValueEnv
  , errors      :: [Message]
  }

type ExpandM a = S.State ExpandState a

getModuleIdent :: ExpandM ModuleIdent
getModuleIdent = S.gets expModIdent

getTyConsEnv :: ExpandM ExpTCEnv
getTyConsEnv = S.gets expTCEnv

getValueEnv :: ExpandM ExpValueEnv
getValueEnv = S.gets expValueEnv

report :: Message -> ExpandM ()
report msg = S.modify $ \ s -> s { errors = msg : errors s }

runExpand :: ExpandM a -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> (a, [Message])
runExpand expand m tcEnv tyEnv =
  let (r, s) = S.runState expand (ExpandState m tcEnv tyEnv [])
  in (r, reverse $ errors s)

expandSpecs :: Maybe ImportSpec -> ExpandM (Maybe ImportSpec)
expandSpecs Nothing                 = return Nothing
expandSpecs (Just (Importing p is)) = (Just . Importing p . concat) `liftM` mapM expandImport is
expandSpecs (Just (Hiding    p is)) = (Just . Hiding    p . concat) `liftM` mapM expandHiding is

expandImport :: Import -> ExpandM [Import]
expandImport (Import         spi x    ) =               expandThing    spi x
expandImport (ImportTypeWith spi tc cs) = (:[]) `liftM` expandTypeWith spi tc cs
expandImport (ImportTypeAll  spi tc   ) = (:[]) `liftM` expandTypeAll  spi tc

expandHiding :: Import -> ExpandM [Import]
expandHiding (Import         spi x    ) = expandHide spi x
expandHiding (ImportTypeWith spi tc cs) = (:[]) `liftM` expandTypeWith spi tc cs
expandHiding (ImportTypeAll  spi tc   ) = (:[]) `liftM` expandTypeAll  spi tc

-- try to expand as type constructor
expandThing :: SpanInfo -> Ident -> ExpandM [Import]
expandThing spi tc = do
  tcEnv <- getTyConsEnv
  case Map.lookup tc tcEnv of
    Just _  -> expandThing' spi tc $ Just [ImportTypeWith spi tc []]
    Nothing -> expandThing' spi tc Nothing

-- try to expand as function / data constructor
expandThing' :: SpanInfo -> Ident -> Maybe [Import] -> ExpandM [Import]
expandThing' spi f tcImport = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  expand m f (Map.lookup f tyEnv) tcImport
  where
  expand :: ModuleIdent -> Ident
         -> Maybe IValueInfo -> Maybe [Import] -> ExpandM [Import]
  expand m e Nothing  Nothing   = report (errUndefinedEntity m e) >> return []
  expand _ _ Nothing  (Just tc) = return tc
  expand m e (Just v) maybeTc
    | isConstr v = case maybeTc of
        Nothing -> report (errImportDataConstr m e) >> return []
        Just tc -> return tc
    | otherwise  = return [Import spi e]

  isConstr (Constr _) = True
  isConstr (Var  _ _) = False

-- try to hide as type constructor
expandHide :: SpanInfo -> Ident -> ExpandM [Import]
expandHide spi tc = do
  tcEnv <- getTyConsEnv
  case Map.lookup tc tcEnv of
    Just _  -> expandHide' spi tc $ Just [ImportTypeWith spi tc []]
    Nothing -> expandHide' spi tc Nothing

-- try to hide as function / data constructor
expandHide' :: SpanInfo -> Ident -> Maybe [Import] -> ExpandM [Import]
expandHide' spi f tcImport = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  case Map.lookup f tyEnv of
    Just _  -> return $ Import spi f : fromMaybe [] tcImport
    Nothing -> case tcImport of
      Nothing -> report (errUndefinedEntity m f) >> return []
      Just tc -> return tc

expandTypeWith :: SpanInfo -> Ident -> [Ident] -> ExpandM Import
expandTypeWith spi tc cs = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  ImportTypeWith spi tc `liftM` case Map.lookup tc tcEnv of
    Just (Data  _ xs) -> mapM (checkElement errUndefinedElement xs) cs
    Just (Class _ xs) -> mapM (checkElement errUndefinedMethod  xs) cs
    Just (Alias    _) -> report (errNonDataTypeOrTypeClass tc) >> return []
    Nothing           -> report (errUndefinedEntity      m tc) >> return []
  where
  -- check if given identifier is constructor or label of type tc
  checkElement err cs' c = do
    unless (c `elem` cs') $ report $ err tc c
    return c

expandTypeAll :: SpanInfo -> Ident -> ExpandM Import
expandTypeAll spi tc = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  ImportTypeWith spi tc `liftM` case Map.lookup tc tcEnv of
    Just (Data _  xs) -> return xs
    Just (Class _ xs) -> return xs
    Just (Alias    _) -> report (errNonDataTypeOrTypeClass tc) >> return []
    Nothing           -> report (errUndefinedEntity      m tc) >> return []

-- error messages

errUndefinedElement :: Ident -> Ident -> Message
errUndefinedElement tc c = spanInfoMessage c $ hsep $ map text
  [ idName c, "is not a constructor or label of type ", idName tc ]

errUndefinedMethod :: Ident -> Ident -> Message
errUndefinedMethod cls f = spanInfoMessage f $ hsep $ map text
  [ idName f, "is not a method of class", idName cls ]

errUndefinedEntity :: ModuleIdent -> Ident -> Message
errUndefinedEntity m x = spanInfoMessage x $ hsep $ map text
  [ "Module", moduleName m, "does not export", idName x ]

errNonDataTypeOrTypeClass :: Ident -> Message
errNonDataTypeOrTypeClass tc = spanInfoMessage tc $ hsep $ map text
  [ idName tc, "is not a data type or type class" ]

errImportDataConstr :: ModuleIdent -> Ident -> Message
errImportDataConstr _ c = spanInfoMessage c $ hsep $ map text
  [ "Explicit import for data constructor", idName c ]
