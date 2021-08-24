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
import           Data.Maybe               (fromMaybe, isJust, isNothing)

import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Base.Pretty
import Curry.Syntax

import Base.CurryKinds (toKind', toClassKind)
import Base.CurryTypes
import Base.Messages (Message, spanInfoMessage, internalError)
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
interfaceCheck pEnv tcEnv clsEnv inEnv tyEnv (Interface m _ ds) =
  reverse (errors s)
  where s = S.execState (mapM_ checkImport ds) initState
        initState = ICState m pEnv tcEnv clsEnv inEnv tyEnv []

checkImport :: IDecl -> IC ()
checkImport (IInfixDecl _ fix pr op) = checkPrecInfo check op op
  where check (PrecInfo op' (OpPrec fix' pr')) =
          op == op' && fix == fix' && pr == pr'
checkImport (HidingDataDecl _ tc k tvs) =
  checkTypeInfo "hidden data type" check tc tc
  where check (DataType     tc' k' _)
          | tc == tc' && toKind' k (length tvs) == k' = Just ok
        check (RenamingType tc' k' _)
          | tc == tc' && toKind' k (length tvs) == k' = Just ok
        check _ = Nothing
checkImport (IDataDecl _ tc k tvs cs _) = checkTypeInfo "data type" check tc tc
  where check (DataType     tc' k' cs')
          | tc == tc' && toKind' k (length tvs) == k' &&
            (null cs || map constrId cs == map constrIdent cs')
          = Just (mapM_ (checkConstrImport tc tvs) cs)
        check (RenamingType tc' k'   _)
          | tc == tc' && toKind' k (length tvs) == k' && null cs
          = Just ok
        check _ = Nothing
checkImport (INewtypeDecl _ tc k tvs nc _) = checkTypeInfo "newtype" check tc tc
  where check (RenamingType tc' k' nc')
          | tc == tc' && toKind' k (length tvs) == k' &&
            nconstrId nc == constrIdent nc'
          = Just (checkNewConstrImport tc tvs nc)
        check _ = Nothing
checkImport (ITypeDecl _ tc k tvs ty) = do
  m <- getModuleIdent
  let check (AliasType tc' k' n' ty')
        | tc == tc' && toKind' k (length tvs) == k' &&
          length tvs == n' && toQualType m tvs ty == ty'
        = Just ok
      check _ = Nothing
  checkTypeInfo "synonym type" check tc tc
checkImport (IFunctionDecl _ f (Just tvs) n ty) = do
  m <- getModuleIdent
  let check (Value f' cm' n' (ForAll _ ty')) =
        f == f' && isJust cm' && n' == n &&
        toQualPredType m tvs ICC ty == ty'
      check _ = False
  checkValueInfo "method" check f f
checkImport (IFunctionDecl _ f Nothing n ty) = do
  m <- getModuleIdent
  let check (Value f' cm' n' (ForAll _ ty')) =
        f == f' && isNothing cm' && n' == n &&
        toQualPredType m [] OPred ty == ty'
      check _ = False
  checkValueInfo "function" check f f
checkImport (HidingClassDecl _ cx cls k clsvars) = do
  clsEnv <- getClassEnv
  let check (TypeClass cls' k' _)
        | cls == cls' && toClassKind k (length clsvars) == k' &&
          map (constraintToSuperClass clsvars) cx == superClasses cls' clsEnv
        = Just ok
      check _ = Nothing
  checkTypeInfo "hidden type class" check cls cls
checkImport (IClassDecl _ cx cls k clsvars ms _) = do
  clsEnv <- getClassEnv
  let check (TypeClass cls' k' fs)
        | cls == cls' && toClassKind k (length clsvars) == k' &&
          map (constraintToSuperClass clsvars) cx == superClasses cls' clsEnv &&
          map (\m -> (imethod m, imethodArity m)) ms ==
            map (\f -> (methodName f, methodArity f)) fs
        = Just $ mapM_ (checkMethodImport cls clsvars) ms
      check _ = Nothing
  checkTypeInfo "type class" check cls cls
checkImport (IInstanceDecl _ cx cls tys is m) =
  checkInstInfo check cls (cls, tys') m
  where PredTypes ps tys' = toPredTypes [] OPred cx tys
        check ps' is' = ps == ps' && sort is == sort is'

checkConstrImport :: QualIdent -> [Ident] -> ConstrDecl -> IC ()
checkConstrImport tc tvs (ConstrDecl _ c tys) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      check (DataConstructor c' _ _ (ForAll uqvs pty)) =
        qc == c' && length tvs == uqvs &&
        qualifyPredType m (toConstrType tc tvs tys) == pty
      check _ = False
  checkValueInfo "data constructor" check c qc
checkConstrImport tc tvs (ConOpDecl _ ty1 op ty2) = do
  m <- getModuleIdent
  let qc = qualifyLike tc op
      check (DataConstructor c' _ _ (ForAll uqvs pty)) =
        qc == c' && length tvs == uqvs &&
        qualifyPredType m (toConstrType tc tvs [ty1, ty2]) == pty
      check _ = False
  checkValueInfo "data constructor" check op qc
checkConstrImport tc tvs (RecordDecl _ c fs) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      (ls, tys) = unzip [(l, ty) | FieldDecl _ labels ty <- fs, l <- labels]
      check (DataConstructor c' _ ls' (ForAll uqvs pty)) =
        qc == c' && length tvs == uqvs && ls == ls' &&
        qualifyPredType m (toConstrType tc tvs tys) == pty
      check _ = False
  checkValueInfo "data constructor" check c qc

checkNewConstrImport :: QualIdent -> [Ident] -> NewConstrDecl -> IC ()
checkNewConstrImport tc tvs (NewConstrDecl _ c ty) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      check (NewtypeConstructor c' _ (ForAll uqvs (PredType _ ty'))) =
        qc == c' && length tvs == uqvs && toQualType m tvs ty == head (arrowArgs ty')
      check _ = False
  checkValueInfo "newtype constructor" check c qc
checkNewConstrImport tc tvs (NewRecordDecl _ c (l, ty)) = do
  m <- getModuleIdent
  let qc = qualifyLike tc c
      check (NewtypeConstructor c' l' (ForAll uqvs (PredType _ ty'))) =
        qc == c' && length tvs == uqvs && l == l' &&
        toQualType m tvs ty == head (arrowArgs ty')
      check _ = False
  checkValueInfo "newtype constructor" check c qc

checkMethodImport :: QualIdent -> [Ident] -> IMethodDecl -> IC ()
checkMethodImport qcls clsvars (IMethodDecl _ f _ qty) =
  checkValueInfo "method" check f qf
  where qf = qualifyLike qcls f
        check (Value f' cm' _ (ForAll _ pty)) =
          qf == f' && isJust cm' &&
          toMethodType qcls clsvars qty == pty
        check _ = False

checkPrecInfo :: HasSpanInfo s => (PrecInfo -> Bool) -> s -> QualIdent -> IC ()
checkPrecInfo check p op = do
  pEnv <- getPrecEnv
  let checkInfo m op' = case qualLookupTopEnv op pEnv of
        []     -> report $ errNoPrecedence p m op'
        [prec] -> unless (check prec)
                         (report $ errImportConflict p "precedence" m op')
        _      -> internalError "checkPrecInfo"
  checkImported checkInfo op

checkTypeInfo :: HasSpanInfo s => String -> (TypeInfo -> Maybe (IC ())) -> s
              -> QualIdent -> IC ()
checkTypeInfo what check p tc = do
  tcEnv <- getTyConsEnv
  let checkInfo m tc' = case qualLookupTopEnv tc tcEnv of
        []   -> report $ errNotExported p what m tc'
        [ti] -> fromMaybe (report $ errImportConflict p what m tc') (check ti)
        _    -> internalError "checkTypeInfo"
  checkImported checkInfo tc

checkInstInfo :: HasSpanInfo s => (PredSet -> [(Ident, Int)] -> Bool) -> s
              -> InstIdent -> Maybe ModuleIdent -> IC ()
checkInstInfo check p i mm = do
  inEnv <- getInstEnv
  let checkInfo m _ = case lookupInstExact i inEnv of
        Just (m', ps, is)
          | m /= m'   -> report $ errNoInstance p m i
          | otherwise ->
            unless (check ps is) $ report $ errInstanceConflict p m i
        Nothing -> report $ errNoInstance p m i
  checkImported checkInfo (maybe qualify qualifyWith mm anonId)

checkValueInfo :: HasSpanInfo a => String -> (ValueInfo -> Bool) -> a
               -> QualIdent -> IC ()
checkValueInfo what check p x = do
  tyEnv <- getValueEnv
  let checkInfo m x' = case qualLookupTopEnv x tyEnv of
        []   -> report $ errNotExported p' what m x'
        [vi] -> unless (check vi)
                  (report $ errImportConflict p' what m x')
        _    -> internalError "checkValueInfo"
  checkImported checkInfo x
  where p' = getSpanInfo p

checkImported :: (ModuleIdent -> Ident -> IC ()) -> QualIdent -> IC ()
checkImported _ (QualIdent _ Nothing  _) = ok
checkImported f (QualIdent _ (Just m) x) = f m x

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errNotExported :: HasSpanInfo s => s -> String -> ModuleIdent -> Ident -> Message
errNotExported p what m x = spanInfoMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Module" <+> text (moduleName m)
  <+> text "does not export"<+> text what <+> text (escName x)

errNoPrecedence :: HasSpanInfo s => s -> ModuleIdent -> Ident -> Message
errNoPrecedence p m x = spanInfoMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Module" <+> text (moduleName m)
  <+> text "does not define a precedence for" <+> text (escName x)

errNoInstance :: HasSpanInfo s => s -> ModuleIdent -> InstIdent -> Message
errNoInstance p m i = spanInfoMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Module" <+> text (moduleName m)
  <+> text "does not define an instance for" <+> ppInstIdent i

errImportConflict :: HasSpanInfo s => s -> String -> ModuleIdent -> Ident -> Message
errImportConflict p what m x = spanInfoMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Declaration of" <+> text what <+> text (escName x)
  <+> text "does not match its definition in module" <+> text (moduleName m)

errInstanceConflict :: HasSpanInfo s => s -> ModuleIdent -> InstIdent -> Message
errInstanceConflict p m i = spanInfoMessage p $
  text "Inconsistent module interfaces"
  $+$ text "Declaration of instance" <+> ppInstIdent i
  <+> text "does not match its definition in module" <+> text (moduleName m)
