{- |
    Module      :  $Header$
    Description :  Environment containing the module's information
    Copyright   :  (c) 2011 - 2015 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines the compilation environment for a single module,
     containing the information needed throughout the compilation process.
-}
module CompilerEnv where

import qualified Data.Map as Map (Map, keys, toList)

import Curry.Base.Ident    (ModuleIdent, moduleName)
import Curry.Base.Pretty
import Curry.Base.Span   (Span)
import Curry.Syntax

import Base.TopEnv (allBindings, allLocalBindings)

import Env.Class
import Env.Instance
import Env.Interface
import Env.ModuleAlias (AliasEnv, initAliasEnv)
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

type CompEnv a = (CompilerEnv, a)

-- |A compiler environment contains information about the module currently
--  compiled. The information is updated during the different stages of
--  compilation.
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent         -- ^ identifier of the module
  , filePath     :: FilePath            -- ^ 'FilePath' of compilation target
  , extensions   :: [KnownExtension]    -- ^ enabled language extensions
  , tokens       :: [(Span, Token)]     -- ^ token list of module
  , interfaceEnv :: InterfaceEnv        -- ^ declarations of imported interfaces
  , aliasEnv     :: AliasEnv            -- ^ aliases for imported modules
  , tyConsEnv    :: TCEnv               -- ^ type constructors and type classes
  , classEnv     :: ClassEnv            -- ^ all type classes with their super classes
  , instEnv      :: InstEnv             -- ^ instances
  , valueEnv     :: ValueEnv            -- ^ functions and data constructors
  , opPrecEnv    :: OpPrecEnv           -- ^ operator precedences
  }

-- |Initial 'CompilerEnv'
initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , filePath     = []
  , extensions   = []
  , tokens       = []
  , interfaceEnv = initInterfaceEnv
  , aliasEnv     = initAliasEnv
  , tyConsEnv    = initTCEnv
  , classEnv     = initClassEnv
  , instEnv      = initInstEnv
  , valueEnv     = initDCEnv
  , opPrecEnv    = initOpPrecEnv
  }

-- |Show the 'CompilerEnv'
showCompilerEnv :: CompilerEnv -> Bool -> Bool -> String
showCompilerEnv env allBinds simpleEnv = show $ vcat
  [ header "Module Identifier  " $ text  $ moduleName $ moduleIdent env
  , header "FilePath"            $ text  $ filePath    env
  , header "Language Extensions" $ text  $ show $ extensions  env
  , header "Interfaces         " $ hcat  $ punctuate comma
                                         $ map (text . moduleName)
                                         $ Map.keys $ interfaceEnv env
  , header "Module Aliases     " $ ppMap simpleEnv $ aliasEnv env
  , header "Precedences        " $ ppAL simpleEnv $ bindings $ opPrecEnv env
  , header "Type Constructors  " $ ppAL simpleEnv $ bindings $ tyConsEnv env
  , header "Classes            " $ ppMap simpleEnv $ classEnv env
  , header "Instances          " $ ppMap simpleEnv $ instEnv env
  , header "Values             " $ ppAL simpleEnv $ bindings $ valueEnv  env
  ]
  where
  header hdr = hang (text hdr <+> colon) 4
  bindings = if allBinds then allBindings else allLocalBindings

-- |Pretty print a 'Map'
ppMap :: (Show a, Pretty a, Show b, Pretty b) => Bool-> Map.Map a b -> Doc
ppMap True  = ppMapPretty
ppMap False = ppMapShow

ppMapShow :: (Show a, Show b) => Map.Map a b -> Doc
ppMapShow = ppALShow . Map.toList

ppMapPretty :: (Pretty a, Pretty b) => Map.Map a b -> Doc
ppMapPretty = ppALPretty . Map.toList

-- |Pretty print an association list
ppAL :: (Show a, Pretty a, Show b, Pretty b) => Bool -> [(a, b)] -> Doc
ppAL True  = ppALPretty
ppAL False = ppALShow

ppALShow :: (Show a, Show b) => [(a, b)] -> Doc
ppALShow xs = vcat
        $ map (\(a,b) -> text (pad a keyWidth) <+> equals <+> text b) showXs
  where showXs   = map (\(a,b) -> (show a, show b)) xs
        keyWidth = maximum (0 : map (length .fst) showXs)
        pad s n  = take n (s ++ repeat ' ')

ppALPretty :: (Pretty a, Pretty b) => [(a, b)] -> Doc
ppALPretty xs = vcat
        $ map (\(a,b) -> text (pad a keyWidth) <+> equals <+> text b) showXs
  where showXs   = map (\(a,b) -> (render (pPrint a), render (pPrint b))) xs
        keyWidth = maximum (0 : map (length .fst) showXs)
        pad s n  = take n (s ++ repeat ' ')
