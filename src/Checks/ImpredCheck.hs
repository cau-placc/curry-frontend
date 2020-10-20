{-|
Module      : Checks.ImpredCheck
Description : Checks for impredicative types
Copyright   : (c) 2019 Jan-Hendrik Matthes
License     : BSD-3-Clause

Maintainer  : fte@informatik.uni-kiel.de
Stability   : experimental
Portability : portable

Checks all data type declarations, type synonyms, class declarations, instance
declarations and type signatures for an impredicative instantiation of type
variables. An error is generated if one is found. It also ensures that
default-declarations contain no universally quantified type variables or
predicates.
-}
module Checks.ImpredCheck (impredCheck) where

import           Control.Monad.Extra (allM, unlessM)
import qualified Control.Monad.State as S (State, gets, modify, runState)

import           Curry.Base.Ident
import           Curry.Base.Pretty
import           Curry.Base.SpanInfo (SpanInfo, HasSpanInfo (..))
import           Curry.Syntax
import           Curry.Syntax.Pretty ()

import           Base.CurryTypes
import           Base.Messages       (Message, spanInfoMessage)

import           Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTypeInfo)

impredCheck :: TCEnv -> Module () -> (Module (), [Message])
impredCheck tcEnv mdl@(Module _ _ _ m _ _ _) =
  runIC (checkModule mdl) $ initState m tcEnv

checkModule :: Module () -> ICM (Module ())
checkModule mdl@(Module _ _ _ _ _ _ ds) = do
  mapM_ checkImpredDecl ds
  return mdl

-- | Impredicativity check monad.
type ICM = S.State ICState

-- | Internal state of the impredicativity check.
data ICState = ICState
  { moduleIdent :: ModuleIdent -- ^ 'ModuleIdent' of the current module.
  , tyConsEnv   :: TCEnv
  , errors      :: [Message]   -- ^ Impredicativity errors in the module.
  }

-- | Initial impredicativity check state.
initState :: ModuleIdent -> TCEnv -> ICState
initState m tcEnv = ICState m tcEnv []

-- | Run the impredicativity check monad.
runIC :: ICM a -> ICState -> (a, [Message])
runIC icm s = let (a, s') = S.runState icm s in (a, reverse $ errors s')

-- | Retrieve the 'ModuleIdent' of the current module.
getModuleIdent :: ICM ModuleIdent
getModuleIdent = S.gets moduleIdent

-- | Retrieve the 'TCEnv'.
getTyConsEnv :: ICM TCEnv
getTyConsEnv = S.gets tyConsEnv

-- | Report an impredicativity error.
report :: Message -> ICM ()
report msg = S.modify $ \s -> s { errors = msg : errors s }

-- | Everything is checked.
ok :: ICM ()
ok = return ()

-- -----------------------------------------------------------------------------
-- Impredicative polymorphism detection
-- -----------------------------------------------------------------------------

checkImpredDecl :: Decl a -> ICM ()
checkImpredDecl (DataDecl _ _ _ cs _)        = mapM_ checkImpredConsDecl cs
checkImpredDecl (NewtypeDecl _ _ _ c _)      = checkImpredNewConsDecl c
checkImpredDecl (TypeDecl _ _ _ ty)          = checkImpredType ty
checkImpredDecl (TypeSig _ _ ty)             = checkImpredType ty
checkImpredDecl (ClassDecl _ _ _ _ _ ds)     = mapM_ checkImpredDecl ds
checkImpredDecl (InstanceDecl _ _ _ _ ty ds) = do
  checkImpredType ty
  mapM_ checkImpredDecl ds
checkImpredDecl (DefaultDecl _ tys)          = mapM_ checkType tys
  where
    checkType te = unlessM (checkSimpleType te) $
      report $ errIllegalDefaultType (getSpanInfo te) te
checkImpredDecl _                            = ok

checkImpredConsDecl :: ConstrDecl -> ICM ()
checkImpredConsDecl (ConstrDecl _ _ tys)    = mapM_ checkImpredType tys
checkImpredConsDecl (ConOpDecl _ ty1 _ ty2) = mapM_ checkImpredType [ty1, ty2]
checkImpredConsDecl (RecordDecl _ _ fs)     = mapM_ checkImpredFieldDecl fs

checkImpredFieldDecl :: FieldDecl -> ICM ()
checkImpredFieldDecl (FieldDecl _ _ ty) = checkImpredType ty

checkImpredNewConsDecl :: NewConstrDecl -> ICM ()
checkImpredNewConsDecl (NewConstrDecl _ _ ty)      = checkImpredType ty
checkImpredNewConsDecl (NewRecordDecl _ _ (_, ty)) = checkImpredType ty

-- | Checks whether the type expression contains no impredicative polymorphism.
checkImpredType :: TypeExpr -> ICM ()
checkImpredType (ConstructorType _ _)      = ok
checkImpredType te@(ApplyType spi ty1 ty2) = do
  unlessM (checkSimpleType ty2) $
    report $ errIllegalPolymorphicType spi te
  checkImpredType ty1
  checkImpredType ty2
checkImpredType (VariableType _ _)         = ok
checkImpredType te@(TupleType spi tys)     = do
  unlessM (allM checkSimpleType tys) $
    report $ errIllegalPolymorphicType spi te
  mapM_ checkImpredType tys
checkImpredType te@(ListType spi ty)       = do
  unlessM (checkSimpleType ty) $
    report $ errIllegalPolymorphicType spi te
  checkImpredType ty
checkImpredType (ArrowType _ ty1 ty2)      = do
  checkImpredType ty1
  checkImpredType ty2
checkImpredType (ParenType _ ty)           = checkImpredType ty
checkImpredType (ContextType _ _ ty)       = checkImpredType ty
checkImpredType (ForallType _ _ ty)        = checkImpredType ty

-- | Checks whether the given type expression contains no universally
-- quantified type variables or type constraints.
checkSimpleType :: TypeExpr -> ICM Bool
checkSimpleType (ConstructorType _ tc) = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  case qualLookupTypeInfo tc tcEnv of
    [AliasType _ _ _ ty] -> checkSimpleType (fromType identSupply ty)
    _ -> case qualLookupTypeInfo (qualQualify m tc) tcEnv of
           [AliasType _ _ _ ty] -> checkSimpleType (fromType identSupply ty)
           _                    -> return True
checkSimpleType (ApplyType _ ty1 ty2)  = allM checkSimpleType [ty1, ty2]
checkSimpleType (VariableType _ _)     = return True
checkSimpleType (TupleType _ tys)      = allM checkSimpleType tys
checkSimpleType (ListType _ ty)        = checkSimpleType ty
checkSimpleType (ArrowType _ ty1 ty2)  = allM checkSimpleType [ty1, ty2]
checkSimpleType (ParenType _ ty)       = checkSimpleType ty
checkSimpleType (ContextType _ _ _)    = return False
checkSimpleType (ForallType _ _ _)     = return False

-- -----------------------------------------------------------------------------
-- Error messages
-- -----------------------------------------------------------------------------

errIllegalPolymorphicType :: SpanInfo -> TypeExpr -> Message
errIllegalPolymorphicType spi ty = spanInfoMessage spi $ vcat
  [ text "Illegal polymorphic type" <+> pPrintPrec 0 ty
  , text "Impredicative polymorphism isn't yet supported."
  ]

errIllegalDefaultType :: SpanInfo -> TypeExpr -> Message
errIllegalDefaultType spi ty = spanInfoMessage spi $ vcat
  [ text "Illegal polymorphic type:" <+> pPrintPrec 0 ty
  , text "When checking the types in a default declaration."
  ]
