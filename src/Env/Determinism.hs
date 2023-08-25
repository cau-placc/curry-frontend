module Env.Determinism where

import Prelude hiding ((<>))
import Data.Map ( Map )
import qualified Data.Map as Map

import Base.Types ( Type )
import Base.PrettyTypes ()
import Curry.Base.Ident ( QualIdent )
import Curry.Base.Pretty ( Pretty(..), parens, dot, text, (<+>), (<>), hsep, parenIf )

type DetEnv = Map IdentInfo DetScheme
type TopDetEnv = DetEnv
data NestDetEnv = Top TopDetEnv
                | LocalEnv NestDetEnv DetEnv

initDetEnv :: DetEnv
initDetEnv = Map.empty

data IdentInfo = QI QualIdent
               | II QualIdent QualIdent QualIdent -- class, tycon, method (only for known instances with the given type constructor)
               | LII QualIdent Type QualIdent -- class, inst type, method (only for locally bound instances from a constraint)
               | CI QualIdent QualIdent -- class, default method
  deriving (Eq, Ord, Show)

instance Pretty IdentInfo where
  pPrint (QI qid) = pPrint qid
  pPrint (II cls tc meth) = parens (pPrint cls <+> pPrint tc) <> dot <> pPrint meth
  pPrint (LII cls ty meth) = parens (pPrint cls <+> text "@" <> pPrint ty) <> dot <> pPrint meth
  pPrint (CI cls meth) = pPrint cls <> dot <> pPrint meth

instance Pretty DetScheme where
  pPrint (Forall [] ty) = pPrint ty
  pPrint (Forall vs ty) = text "forall" <+> hsep (map (pPrint . VarTy) vs) <> dot <> pPrint ty

instance Pretty DetType where
  pPrintPrec _ (VarTy v) = text "a" <> pPrint v
  pPrintPrec _ Det = text "Det"
  pPrintPrec _ Nondet = text "Nondet"
  pPrintPrec p (DetArrow ty1 ty2) = parenIf (p > 0) $
    pPrintPrec 1 ty1 <+> text "->" <+> pPrintPrec 0 ty2

bindNestEnv :: IdentInfo -> DetScheme -> NestDetEnv -> NestDetEnv
bindNestEnv ii ty (Top env) = Top (Map.insert ii ty env)
bindNestEnv ii ty (LocalEnv inner lcl) = LocalEnv inner (Map.insert ii ty lcl)

nestEnv :: NestDetEnv -> NestDetEnv
nestEnv env = LocalEnv env Map.empty

unnestEnv :: NestDetEnv -> NestDetEnv
unnestEnv (Top env) = Top env
unnestEnv (LocalEnv env _) = env

extractTopEnv :: NestDetEnv -> TopDetEnv
extractTopEnv (Top env) = env
extractTopEnv (LocalEnv env _) = extractTopEnv env

lookupNestEnv :: IdentInfo -> NestDetEnv -> Maybe DetScheme
lookupNestEnv ii (Top env) = Map.lookup ii env
lookupNestEnv ii (LocalEnv env lcl) = case Map.lookup ii lcl of
  Just ty -> Just ty
  Nothing -> lookupNestEnv ii env

mapNestEnv :: (DetScheme -> DetScheme) -> NestDetEnv -> NestDetEnv
mapNestEnv f (Top env) = Top (Map.map f env)
mapNestEnv f (LocalEnv env lcl) = LocalEnv (mapNestEnv f env) (Map.map f lcl)

flattenNestEnv :: NestDetEnv -> DetEnv
flattenNestEnv (Top env) = env
flattenNestEnv (LocalEnv env lcl) = Map.union lcl (flattenNestEnv env)

type VarIndex = Int

data DetType = VarTy VarIndex
             | Det
             | DetArrow DetType DetType
             | Nondet
  deriving (Eq, Ord, Show)

data DetConstraint = EqualType VarIndex DetType -- v ~ alpha
                   | AppliedType VarIndex VarIndex [DetType] -- v ~ y @ alpha1 ... alphan
  deriving (Eq, Ord, Show)

data DetScheme = Forall [VarIndex] DetType
  deriving (Eq, Ord, Show)

toSchema :: DetType -> DetScheme
toSchema = Forall []
