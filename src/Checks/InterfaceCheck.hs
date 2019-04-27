{- |
    Module      :  $Header$
    Description :  Checks consistency of interface files
    Copyright   :  (c) 2000 - 2007 Wolfgang Lux
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   Interface files include declarations of all entities that are exported
   by the module, but defined in another module. Since these declarations
   can become inconsistent if client modules are not recompiled properly,
   the compiler checks that all imported declarations in an interface
   agree with their original definitions.

   One may ask why we include imported declarations at all, if the
   compiler always has to compare those declarations with the original
   definitions. The main reason for this is that it helps to avoid
   unnecessary recompilations of client modules. As an example, consider
   the three modules:

     module A where { data T = C }
     module B(T(..)) where { import A }
     module C where { import B; f = C }

   where module B could be considered as a public interface of module A,
   which restricts access to type A.T and its constructor C.
   The client module C imports this type via the public interface B.
   If now module A is changed by adding a definition of a new global function

     module A where { data T = C; f = C }

   module B must be recompiled because A's interface is changed.
   On the other hand, module C need not be recompiled because the change in
   A does not affect B's interface. By including the declaration of type A.T
   in B's interface, the compiler can trivially check that B's interface
   remains unchanged and therefore the client module C is not recompiled.

   Another reason for including imported declarations in interfaces is
   that the compiler in principle could avoid loading interfaces of
   modules that are imported only indirectly, which would save processing
   time and allow distributing binary packages of a library with a public
   interface module only. However, this has not been implemented yet.
-}

module Checks.InterfaceCheck (interfaceCheck) where

import           Control.Monad            (unless)
import qualified Control.Monad.State as S
import           Data.List                (sort)
import           Data.Maybe               (fromMaybe)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax

import Base.CurryKinds (toKind')
import Base.CurryTypes
import Base.Messages (Message, posMessage, internalError)
import Base.TopEnv
import Base.Types

import Env.Class
import Env.Instance
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

data ICState = ICState
  { moduleIdent :: ModuleIdent
  , precEnv     :: OpPrecEnv
  , tyConsEnv   :: TCEnv
  , classEnv    :: ClassEnv
  , instEnv     :: InstEnv
  , valueEnv    :: ValueEnv
  , errors      :: [Message]
  }

type IC = S.State ICState

getModuleIdent :: IC ModuleIdent
getModuleIdent = S.gets moduleIdent

getPrecEnv :: IC OpPrecEnv
getPrecEnv = S.gets precEnv

getTyConsEnv :: IC TCEnv
getTyConsEnv = S.gets tyConsEnv

getClassEnv :: IC ClassEnv
getClassEnv = S.gets classEnv

getInstEnv :: IC InstEnv
getInstEnv = S.gets instEnv

getValueEnv :: IC ValueEnv
getValueEnv = S.gets valueEnv

-- |Report a syntax error
report :: Message -> IC ()
report msg = S.modify $ \s -> s { errors = msg : errors s }

ok :: IC ()
ok = return ()

interfaceCheck :: OpPrecEnv -> TCEnv -> ClassEnv -> InstEnv -> ValueEnv
               -> Interface -> [Message]
interfaceCheck pEnv tcEnv clsEnv inEnv tyEnv (Interface m _ ds) = reverse (errors s)
  where s = S.execState (mapM_ checkImport ds) initState
        initState = ICState m pEnv tcEnv clsEnv inEnv tyEnv []

checkImport :: IDecl -> IC ()
checkImport (IInfixDecl p fix pr op) = checkPrecInfo check p op
  where check (PrecInfo op' (OpPrec fix' pr')) =
          op == op' && fix == fix' && pr == pr'
checkImport (HidingDataDecl p tc k tvs) =
  checkTypeInfo "hidden data type" check p tc
  where check (DataType     tc' k' _)
          | tc == tc' && toKind' k (length tvs) == k' = Just ok
        check (RenamingType tc' k' _)
          | tc == tc' && toKind' k (length tvs) == k' = Just ok
        check _ = Nothing
checkImport (IDataDecl p tc k tvs cs _) = checkTypeInfo "data type" check p tc
  where check (DataType     tc' k' cs')
          | tc == tc' && toKind' k (length tvs) == k' &&
            (null cs || map constrId cs == map constrIdent cs')
          = Just (mapM_ (checkConstrImport tc tvs) cs)
        check (RenamingType tc' k'   _)
          | tc == tc' && toKind' k (length tvs) == k' && null cs
          = Just ok
        check _ = Nothing
checkImport (INewtypeDecl p tc k tvs nc _) = checkTypeInfo "newtype" check p tc
  where check (RenamingType tc' k' nc')
          | tc == tc' && toKind' k (length tvs) == k' &&
            nconstrId nc == constrIdent nc'
          = Just (checkNewConstrImport tc tvs nc)
        check _ = Nothing
checkImport (ITypeDecl p tc k tvs ty) = do
  m <- getModuleIdent
  let check (AliasType tc' k' n' ty')
        | tc == tc' && toKind' k (length tvs) == k' &&
          length tvs == n' && toQualType m tvs ty == ty'
        = Just ok
      check _ = Nothing
  checkTypeInfo "synonym type" check p tc
checkImport (IFunctionDecl p f (Just tv) n ty) = do
  m <- getModuleIdent
  let check (Value f' cm' n' (ForAll _ ty')) =
        f == f' && cm' && n' == n && toQualPredType m [tv] ty == ty'
      check _ = False
  checkValueInfo "method" check p f
checkImport (IFunctionDecl p f Nothing n ty) = do
  m <- getModuleIdent
  let check (Value f' cm' n' (ForAll _ ty')) =
        f == f' && not cm' && n' == n && toQualPredType m [] ty == ty'
      check _ = False
  checkValueInfo "function" check p f
checkImport (HidingClassDecl p cx cls k _) = do
  clsEnv <- getClassEnv
  let check (TypeClass cls' k' _)
        | cls == cls' && toKind' k 0 == k' &&
          [cls'' | Constraint _ cls'' _ <- cx] == superClasses cls' clsEnv
        = Just ok
      check _ = Nothing
  checkTypeInfo "hidden type class" check p cls
checkImport (IClassDecl p cx cls k clsvar ms _) = do
  clsEnv <- getClassEnv
  let check (TypeClass cls' k' fs)
        | cls == cls' && toKind' k 0 == k' &&
          [cls'' | Constraint _ cls'' _ <- cx] == superClasses cls' clsEnv &&
          map (\m -> (imethod m, imethodArity m)) ms ==
            map (\f -> (methodName f, methodArity f)) fs
        = Just $ mapM_ (checkMethodImport cls clsvar) ms
      check _ = Nothing
  checkTypeInfo "type class" check p cls
checkImport (IInstanceDecl p cx cls ty is m) =
  checkInstInfo check p (cls, typeConstr ty) m
  where PredType ps _ = toPredType [] $ QualTypeExpr NoSpanInfo cx ty
        check ps' is' = ps == ps' && sort is == sort is'

checkConstrImport :: QualIdent -> [Ident] -> ConstrDecl -> IC ()
checkConstrImport tc tvs (ConstrDecl p _ cx c tys) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      check (DataConstructor c' _ _ (ForAll uqvs pty)) =
        qc == c' && length tvs == uqvs &&
        qualifyPredType m (toConstrType tc tvs cx tys) == pty
      check _ = False
  checkValueInfo "data constructor" check p qc
checkConstrImport tc tvs (ConOpDecl p _ cx ty1 op ty2) = do
  m <- getModuleIdent
  let qc = qualifyLike tc op
      check (DataConstructor c' _ _ (ForAll uqvs pty)) =
        qc == c' && length tvs == uqvs &&
        qualifyPredType m (toConstrType tc tvs cx [ty1, ty2]) == pty
      check _ = False
  checkValueInfo "data constructor" check p qc
checkConstrImport tc tvs (RecordDecl p _ cx c fs) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      (ls, tys) = unzip [(l, ty) | FieldDecl _ labels ty <- fs, l <- labels]
      check (DataConstructor c' _ ls' (ForAll uqvs pty)) =
        qc == c' && length tvs == uqvs && ls == ls' &&
        qualifyPredType m (toConstrType tc tvs cx tys) == pty
      check _ = False
  checkValueInfo "data constructor" check p qc

checkNewConstrImport :: QualIdent -> [Ident] -> NewConstrDecl -> IC ()
checkNewConstrImport tc tvs (NewConstrDecl p c ty) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      check (NewtypeConstructor c' _ (ForAll uqvs (PredType _ ty'))) =
        qc == c' && length tvs == uqvs &&toQualType m tvs ty == head (arrowArgs ty')
      check _ = False
  checkValueInfo "newtype constructor" check p qc
checkNewConstrImport tc tvs (NewRecordDecl p c (l, ty)) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      check (NewtypeConstructor c' l' (ForAll uqvs (PredType _ ty'))) =
        qc == c' && length tvs == uqvs && l == l' &&
        toQualType m tvs ty == head (arrowArgs ty')
      check _ = False
  checkValueInfo "newtype constructor" check p qc

checkMethodImport :: QualIdent -> Ident -> IMethodDecl -> IC ()
checkMethodImport qcls clsvar (IMethodDecl p f _ qty) =
  checkValueInfo "method" check p qf
  where qf = qualifyLike qcls f
        check (Value f' cm' _ (ForAll _ pty)) =
          qf == f' && cm' && toMethodType qcls clsvar qty == pty
        check _ = False

checkPrecInfo :: (PrecInfo -> Bool) -> Position -> QualIdent -> IC ()
checkPrecInfo check p op = do
  pEnv <- getPrecEnv
  let checkInfo m op' = case qualLookupTopEnv op pEnv of
        []     -> report $ errNoPrecedence p m op'
        [prec] -> unless (check prec)
                         (report $ errImportConflict p "precedence" m op')
        _      -> internalError "checkPrecInfo"
  checkImported checkInfo op

checkTypeInfo :: String -> (TypeInfo -> Maybe (IC ())) -> Position
              -> QualIdent -> IC ()
checkTypeInfo what check p tc = do
  tcEnv <- getTyConsEnv
  let checkInfo m tc' = case qualLookupTopEnv tc tcEnv of
        []   -> report $ errNotExported p what m tc'
        [ti] -> fromMaybe (report $ errImportConflict p what m tc') (check ti)
        _    -> internalError "checkTypeInfo"
  checkImported checkInfo tc

checkInstInfo :: (PredSet -> [(Ident, Int)] -> Bool) -> Position -> InstIdent
              -> Maybe ModuleIdent -> IC ()
checkInstInfo check p i mm = do
  inEnv <- getInstEnv
  let checkInfo m _ = case lookupInstInfo i inEnv of
        Just (m', ps, is)
          | m /= m'   -> report $ errNoInstance p m i
          | otherwise ->
            unless (check ps is) $ report $ errInstanceConflict p m i
        Nothing -> report $ errNoInstance p m i
  checkImported checkInfo (maybe qualify qualifyWith mm anonId)

checkValueInfo :: HasPosition a => String -> (ValueInfo -> Bool) -> a
               -> QualIdent -> IC ()
checkValueInfo what check p x = do
  tyEnv <- getValueEnv
  let checkInfo m x' = case qualLookupTopEnv x tyEnv of
        []   -> report $ errNotExported p' what m x'
        [vi] -> unless (check vi)
                  (report $ errImportConflict p' what m x')
        _    -> internalError "checkValueInfo"
  checkImported checkInfo x
  where p' = getPosition p

checkImported :: (ModuleIdent -> Ident -> IC ()) -> QualIdent -> IC ()
checkImported _ (QualIdent _ Nothing  _) = ok
checkImported f (QualIdent _ (Just m) x) = f m x

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errNotExported :: Position -> String -> ModuleIdent -> Ident -> Message
errNotExported p what m x = posMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Module" <+> text (moduleName m)
  <+> text "does not export"<+> text what <+> text (escName x)

errNoPrecedence :: Position -> ModuleIdent -> Ident -> Message
errNoPrecedence p m x = posMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Module" <+> text (moduleName m)
  <+> text "does not define a precedence for" <+> text (escName x)

errNoInstance :: Position -> ModuleIdent -> InstIdent -> Message
errNoInstance p m i = posMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Module" <+> text (moduleName m)
  <+> text "does not define an instance for" <+> ppInstIdent i

errImportConflict :: Position -> String -> ModuleIdent -> Ident -> Message
errImportConflict p what m x = posMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Declaration of" <+> text what <+> text (escName x)
  <+> text "does not match its definition in module" <+> text (moduleName m)

errInstanceConflict :: Position -> ModuleIdent -> InstIdent -> Message
errInstanceConflict p m i = posMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Declaration of instance" <+> ppInstIdent i
  <+> text "does not match its definition in module" <+> text (moduleName m)
