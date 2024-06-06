{- |
    Module      :  $Header$
    Description :  Compiler options
    Copyright   :  (c) 2005        Martin Engelke
                       2007        Sebastian Fischer
                       2011 - 2016 Björn Peemöller
                       2016 - 2017 Finn Teegen
                       2018        Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines data structures holding options for the
    compilation of Curry programs, and utility functions for printing
    help information as well as parsing the command line arguments.
-}
module CompilerOpts
  ( Options (..), CppOpts (..), PrepOpts (..), WarnOpts (..), DebugOpts (..)
  , OptimizationOpts(..), CaseMode (..), FrontendMode (..), Verbosity (..)
  , TargetType (..), WarnFlag (..), KnownExtension (..), DumpLevel (..)
  , dumpLevel
  , defaultOptions, defaultPrepOpts, defaultWarnOpts, defaultDebugOpts, defaultCppOpts
  , getCompilerOpts, updateOpts, usage, parseOpts
  ) where

import           Data.List             (intercalate, nub)
import           Data.Maybe            (isJust)
import           Data.Char             (isDigit)
import qualified Data.Map    as Map    (Map, empty, insert)
import System.Console.GetOpt
import System.Environment              (getArgs, getProgName)
import System.FilePath                 ( addTrailingPathSeparator, normalise
                                       , splitSearchPath )

import Curry.Files.Filenames           (defaultOutDir)
import Curry.Syntax.Extension

-- -----------------------------------------------------------------------------
-- Option data structures
-- -----------------------------------------------------------------------------

-- |Compiler options
data Options = Options
  -- general
  { optMode          :: FrontendMode          -- ^ modus operandi
  , optVerbosity     :: Verbosity           -- ^ verbosity level
  -- compilation
  , optForce         :: Bool                -- ^ force (re-)compilation of target
  , optLibraryPaths  :: [FilePath]          -- ^ directories to search in
                                            --   for libraries
  , optImportPaths   :: [FilePath]          -- ^ directories to search in
                                            --   for imports
  , optOutDir        :: FilePath            -- ^ output directory for FlatCurry, ...
  , optHtmlDir       :: Maybe FilePath      -- ^ output directory for HTML
  , optUseOutDir     :: Bool                -- ^ use subdir for output?
  , optInterface     :: Bool                -- ^ create a FlatCurry interface file?
  , optOriginPragmas :: Bool                -- ^ emit origin pragmas in interfaces
  , optPrepOpts      :: PrepOpts            -- ^ preprocessor options
  , optWarnOpts      :: WarnOpts            -- ^ warning options
  , optTargetTypes   :: [TargetType]        -- ^ what to generate
  , optExtensions    :: [KnownExtension]    -- ^ enabled language extensions
  , optDebugOpts     :: DebugOpts           -- ^ debug options
  , optCaseMode      :: CaseMode            -- ^ case mode
  , optCppOpts       :: CppOpts             -- ^ C preprocessor options
  , optOptimizations :: OptimizationOpts -- ^ Optimization options
  } deriving Show

-- |C preprocessor options
data CppOpts = CppOpts
  { cppRun         :: Bool                -- ^ run C preprocessor
  , cppDefinitions :: Map.Map String Int  -- ^ defintions for the C preprocessor
  } deriving Show

-- |Preprocessor options
data PrepOpts = PrepOpts
  { ppPreprocess :: Bool      -- ^ apply custom preprocessor
  , ppCmd        :: String    -- ^ preprocessor command
  , ppOpts       :: [String]  -- ^ preprocessor options
  } deriving Show

data CaseMode
  = CaseModeCurry
  | CaseModeFree
  | CaseModeHaskell
  | CaseModeProlog
  | CaseModeGoedel
  deriving (Eq, Show)

-- |Warning options
data WarnOpts = WarnOpts
  { wnWarn         :: Bool       -- ^ show warnings? (legacy option)
  , wnWarnFlags    :: [WarnFlag] -- ^ Warnings flags (see below)
  , wnWarnAsError  :: Bool       -- ^ Should warnings be treated as errors?
  } deriving Show

-- |Debug options
data DebugOpts = DebugOpts
  { dbDumpLevels      :: [DumpLevel] -- ^ dump levels
  , dbDumpEnv         :: Bool        -- ^ dump compilation environment
  , dbDumpRaw         :: Bool        -- ^ dump data structure
  , dbDumpAllBindings :: Bool        -- ^ dump all bindings instead of just the
                                     --   local bindings
  , dbDumpSimple      :: Bool        -- ^ print more readable environments
  } deriving Show

data OptimizationOpts = OptimizationOpts
  { optDesugarNewtypes     :: Bool -- ^ Desugar newtypes
  , optInlineDictionaries  :: Bool -- ^ Inline type class dictionaries
  , optRemoveUnusedImports :: Bool -- ^ Remove unused imports in IL
  , optAddFailed           :: Bool -- ^ add failed match for missing constructors in cases
  } deriving Show

-- | Default compiler options
defaultOptions :: Options
defaultOptions = Options
  { optMode          = ModeMake
  , optVerbosity     = VerbStatus
  , optForce         = False
  , optLibraryPaths  = []
  , optImportPaths   = []
  , optOutDir        = defaultOutDir
  , optHtmlDir       = Nothing
  , optUseOutDir     = True
  , optInterface     = True
  , optOriginPragmas = False
  , optPrepOpts      = defaultPrepOpts
  , optWarnOpts      = defaultWarnOpts
  , optTargetTypes   = []
  , optExtensions    = kielExtensions
  , optDebugOpts     = defaultDebugOpts
  , optCaseMode      = CaseModeCurry
  , optCppOpts       = defaultCppOpts
  , optOptimizations = defaultOptimizationOpts
  }

-- | Default C preprocessor options
defaultCppOpts :: CppOpts
defaultCppOpts = CppOpts
  { cppRun         = False
  , cppDefinitions = Map.empty
  }

-- | Default preprocessor options
defaultPrepOpts :: PrepOpts
defaultPrepOpts = PrepOpts
  { ppPreprocess = False
  , ppCmd        = ""
  , ppOpts       = []
  }

-- | Default warning options
defaultWarnOpts :: WarnOpts
defaultWarnOpts = WarnOpts
  { wnWarn        = True
  , wnWarnFlags   = stdWarnFlags
  , wnWarnAsError = False
  }

-- | Default dump options
defaultDebugOpts :: DebugOpts
defaultDebugOpts = DebugOpts
  { dbDumpLevels      = []
  , dbDumpEnv         = False
  , dbDumpRaw         = False
  , dbDumpAllBindings = False
  , dbDumpSimple      = False
  }

defaultOptimizationOpts :: OptimizationOpts
defaultOptimizationOpts = OptimizationOpts
  { optDesugarNewtypes     = False
  , optInlineDictionaries  = True
  , optRemoveUnusedImports = True
  , optAddFailed           = False
  }

-- |Modus operandi of the program
data FrontendMode
  = ModeHelp           -- ^ Show help information and exit
  | ModeVersion        -- ^ Show version and exit
  | ModeNumericVersion -- ^ Show numeric version, suitable for later processing
  | ModeMake           -- ^ Compile with dependencies
  deriving (Eq, Show)

-- |Verbosity level
data Verbosity
  = VerbQuiet  -- ^ be quiet
  | VerbStatus -- ^ show status of compilation
  deriving (Eq, Ord, Show)

-- |Description and flag of verbosities
verbosities :: [(Verbosity, String, String)]
verbosities = [ ( VerbQuiet , "0", "quiet" )
              , ( VerbStatus, "1", "status")
              ]

-- |Type of the target file
data TargetType
  = Tokens               -- ^ Source code tokens
  | Comments             -- ^ Source code comments
  | Parsed               -- ^ Parsed source code
  | FlatCurry            -- ^ FlatCurry
  | AnnotatedFlatCurry   -- ^ Annotated FlatCurry
  | TypedFlatCurry       -- ^ Typed FlatCurry
  | TypedBinaryFlatCurry -- ^ Typed FlatCurry
  | AbstractCurry        -- ^ AbstractCurry
  | UntypedAbstractCurry -- ^ Untyped AbstractCurry
  | Html                 -- ^ HTML documentation
  | AST                  -- ^ Abstract-Syntax-Tree after checks
  | ShortAST             -- ^ Abstract-Syntax-Tree with shortened decls
    deriving (Eq, Show)

-- |Warnings flags
data WarnFlag
  = WarnMultipleImports      -- ^ Warn for multiple imports
  | WarnDisjoinedRules       -- ^ Warn for disjoined function rules
  | WarnUnusedGlobalBindings -- ^ Warn for unused global bindings
  | WarnUnusedBindings       -- ^ Warn for unused local bindings
  | WarnNameShadowing        -- ^ Warn for name shadowing
  | WarnImportNameShadowing  -- ^ Warn for shadowing of imported names
  | WarnOverlapping          -- ^ Warn for overlapping rules/alternatives
  | WarnIncompletePatterns   -- ^ Warn for incomplete pattern matching
  | WarnMissingSignatures    -- ^ Warn for missing type signatures
  | WarnMissingMethods       -- ^ Warn for missing method implementations
  | WarnOrphanInstances      -- ^ Warn for orphan instances
  | WarnRedundantContext     -- ^ Warn for redundant context in type signatures
    deriving (Eq, Bounded, Enum, Show)

-- |Warning flags enabled by default
stdWarnFlags :: [WarnFlag]
stdWarnFlags =
  [ WarnMultipleImports   , WarnDisjoinedRules   --, WarnUnusedGlobalBindings
  , WarnUnusedBindings    , WarnNameShadowing    , WarnOverlapping
  , WarnIncompletePatterns, WarnMissingSignatures, WarnMissingMethods
  , WarnRedundantContext
  ]

-- |Description and flag of warnings flags
warnFlags :: [(WarnFlag, String, String)]
warnFlags =
  [ ( WarnMultipleImports     , "multiple-imports"
    , "multiple imports"               )
  , ( WarnDisjoinedRules      , "disjoined-rules"
    , "disjoined function rules"       )
  , ( WarnUnusedGlobalBindings, "unused-global-bindings"
    , "unused bindings"                )
  , ( WarnUnusedBindings      , "unused-bindings"
    , "unused bindings"                )
  , ( WarnNameShadowing       , "name-shadowing"
    , "name shadowing"                 )
  , ( WarnImportNameShadowing , "import-name-shadowing"
    , "import name shadowing"          )
  , ( WarnOverlapping         , "overlapping"
    , "overlapping function rules"     )
  , ( WarnIncompletePatterns  , "incomplete-patterns"
    , "incomplete pattern matching"    )
  , ( WarnMissingSignatures   , "missing-signatures"
    , "missing type signatures"        )
  , ( WarnMissingMethods      , "missing-methods"
    , "missing method implementations" )
  , ( WarnOrphanInstances     , "orphan-instances"
    , "orphan instances"               )
  , ( WarnRedundantContext    , "redundant-context"
    , "redundant context")
  ]

-- |Dump level
data DumpLevel
  = DumpCondCompiled      -- ^ dump source code after conditional compiling
  | DumpParsed            -- ^ dump source code after parsing
  | DumpExtensionChecked  -- ^ dump source code after extension checking
  | DumpCaseModeChecked   -- ^ dump source code after case mode checking
  | DumpTypeSyntaxChecked -- ^ dump source code after type syntax checking
  | DumpKindChecked       -- ^ dump source code after kind checking
  | DumpSyntaxChecked     -- ^ dump source code after syntax checking
  | DumpPrecChecked       -- ^ dump source code after precedence checking
  | DumpDeriveChecked     -- ^ dump source code after derive checking
  | DumpInstanceChecked   -- ^ dump source code after instance checking
  | DumpTypeChecked       -- ^ dump source code after type checking
  | DumpExportChecked     -- ^ dump source code after export checking
  | DumpQualified         -- ^ dump source code after qualification
  | DumpDerived           -- ^ dump source code after deriving
  | DumpDesugared         -- ^ dump source code after desugaring
  | DumpDictionaries      -- ^ dump source code after dictionary transformation
  | DumpNewtypes          -- ^ dump source code after removing newtype constructors
  | DumpSimplified        -- ^ dump source code after simplification
  | DumpLifted            -- ^ dump source code after lambda-lifting
  | DumpTranslated        -- ^ dump IL code after translation
  | DumpCaseCompleted     -- ^ dump IL code after case completion
  | DumpTypedFlatCurry    -- ^ dump typed FlatCurry code
  | DumpFlatCurry         -- ^ dump FlatCurry code
    deriving (Eq, Bounded, Enum, Show)

-- |Description and flag of dump levels
dumpLevel :: [(DumpLevel, String, String)]
dumpLevel = [ (DumpCondCompiled     , "dump-cond" , "conditional compiling"           )
            , (DumpParsed           , "dump-parse", "parsing"                         )
            , (DumpExtensionChecked , "dump-exc"  , "extension checking"              )
            , (DumpCaseModeChecked  , "dump-cmc"  , "case mode checking"              )
            , (DumpTypeSyntaxChecked, "dump-tsc"  , "type syntax checking"            )
            , (DumpKindChecked      , "dump-kc"   , "kind checking"                   )
            , (DumpSyntaxChecked    , "dump-sc"   , "syntax checking"                 )
            , (DumpPrecChecked      , "dump-pc"   , "precedence checking"             )
            , (DumpDeriveChecked    , "dump-dc"   , "derive checking"                 )
            , (DumpInstanceChecked  , "dump-inc"  , "instance checking"               )
            , (DumpTypeChecked      , "dump-tc"   , "type checking"                   )
            , (DumpExportChecked    , "dump-ec"   , "export checking"                 )
            , (DumpQualified        , "dump-qual" , "qualification"                   )
            , (DumpDerived          , "dump-deriv", "deriving"                        )
            , (DumpDesugared        , "dump-ds"   , "desugaring"                      )
            , (DumpDictionaries     , "dump-dict" , "dictionary insertion"            )
            , (DumpNewtypes         , "dump-new"  , "removing newtype constructors"   )
            , (DumpLifted           , "dump-lift" , "lifting"                         )
            , (DumpSimplified       , "dump-simpl", "simplification"                  )
            , (DumpTranslated       , "dump-trans", "pattern matching compilation"    )
            , (DumpCaseCompleted    , "dump-cc"   , "case completion"                 )
            , (DumpTypedFlatCurry   , "dump-tflat", "translation into typed FlatCurry")
            , (DumpFlatCurry        , "dump-flat" , "translation into FlatCurry"      )
            ]

-- |Description and flag of language extensions
extensions :: [(KnownExtension, String, String)]
extensions =
  [ ( AnonFreeVars             , "AnonFreeVars"
    , "enable anonymous free variables"              )
  , ( CPP                      , "CPP"
    , "run C preprocessor"                           )
  , ( FunctionalPatterns       , "FunctionalPatterns"
    , "enable functional patterns"                   )
  , ( NegativeLiterals         , "NegativeLiterals"
    , "desugar negated literals as negative literal" )
  , ( NoAnonFreeVars           , "NoAnonFreeVars"
    , "disable anonymous free variables"             )
  , ( NoFunctionalPatterns     , "NoFunctionalPatterns"
    , "disable functional patterns"                  )
  , ( NoImplicitPrelude        , "NoImplicitPrelude"
    , "do not implicitly import the Prelude"         )
  , ( NoDataDeriving           , "NoDataDeriving"
    , "do not implicitly derive the Data class"      )
  ]

-- -----------------------------------------------------------------------------
-- Parsing of the command line options.
--
-- Because some flags require additional arguments, the structure is slightly
-- more complicated to enable malformed arguments to be reported.
-- -----------------------------------------------------------------------------

-- |Instead of just returning the resulting 'Options' structure, we also
-- collect errors from arguments passed to specific options.
type OptErr = (Options, [String])

-- |An 'OptErrTable' consists of a list of entries of the following form:
--   * a flag to be recognized on the command line
--   * an explanation text for the usage information
--   * a modification funtion adjusting the options structure
-- The type is parametric about the option's type to adjust.
type OptErrTable opt = [(String, String, opt -> opt)]

onOpts :: (Options -> Options) -> OptErr -> OptErr
onOpts f (opts, errs) = (f opts, errs)

onCppOpts :: (CppOpts -> CppOpts) -> OptErr -> OptErr
onCppOpts f (opts, errs) = (opts { optCppOpts = f (optCppOpts opts) }, errs)

onPrepOpts :: (PrepOpts -> PrepOpts) -> OptErr -> OptErr
onPrepOpts f (opts, errs) = (opts { optPrepOpts = f (optPrepOpts opts) }, errs)

onWarnOpts :: (WarnOpts -> WarnOpts) -> OptErr -> OptErr
onWarnOpts f (opts, errs) = (opts { optWarnOpts = f (optWarnOpts opts) }, errs)

onDebugOpts :: (DebugOpts -> DebugOpts) -> OptErr -> OptErr
onDebugOpts f (opts, errs)
  = (opts { optDebugOpts = f (optDebugOpts opts) }, errs)

onOptimOpts :: (OptimizationOpts -> OptimizationOpts) -> OptErr -> OptErr
onOptimOpts f (opts, errs)
    = (opts { optOptimizations = f (optOptimizations opts) }, errs)

withArg :: ((a -> b) -> OptErr -> OptErr)
        -> (String -> a -> b) -> String -> OptErr -> OptErr
withArg lift f arg = lift (f arg)

addErr :: String -> OptErr -> OptErr
addErr err (opts, errs) = (opts, errs ++ [err])

mkOptDescr :: ((opt -> opt) -> OptErr -> OptErr)
           -> String -> [String] -> String -> String -> OptErrTable opt
           -> OptDescr (OptErr -> OptErr)
mkOptDescr lift flags longFlags arg what tbl = Option flags longFlags
  (ReqArg (parseOptErr lift what tbl) arg)
  ("set " ++ what ++ " `" ++ arg ++ "', where `" ++ arg ++ "' is one of\n"
    ++ renderOptErrTable tbl)

parseOptErr :: ((opt -> opt) -> OptErr -> OptErr)
            -> String -> OptErrTable opt -> String -> OptErr -> OptErr
parseOptErr lift what table opt = case lookup3 opt table of
  Just f  -> lift f
  Nothing -> addErr $ "unrecognized " ++ what ++ '`' : opt ++ "'\n"
  where
  lookup3 _ []                  = Nothing
  lookup3 k ((k', _, v2) : kvs)
    | k == k'                   = Just v2
    | otherwise                 = lookup3 k kvs

renderOptErrTable :: OptErrTable opt -> String
renderOptErrTable ds
  = intercalate "\n" $ map (\(k, d, _) -> "  " ++ rpad maxLen k ++ ": " ++ d) ds
  where
  maxLen = maximum $ map (\(k, _, _) -> length k) ds
  rpad n x = x ++ replicate (n - length x) ' '

-- | All available compiler options
options :: [OptDescr (OptErr -> OptErr)]
options =
  -- modus operandi
  [ Option "h?" ["help"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeHelp }))
      "display this help and exit"
  , Option "V"  ["version"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeVersion }))
      "show the version number and exit"
  , Option ""   ["numeric-version"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeNumericVersion }))
      "show the numeric version number and exit"
  -- verbosity
  , mkOptDescr onOpts "v" ["verbosity"] "n" "verbosity level" verbDescriptions
  , Option "q"  ["no-verb"]
      (NoArg (onOpts $ \ opts -> opts { optVerbosity = VerbQuiet } ))
      "set verbosity level to quiet"
  -- compilation
  , Option "f"  ["force"]
      (NoArg (onOpts $ \ opts -> opts { optForce = True }))
      "force compilation of target file"
  , Option "P"  ["lib-dir"]
      (ReqArg (withArg onOpts $ \ arg opts -> opts { optLibraryPaths =
        nub $ optLibraryPaths opts ++ splitSearchPath arg}) "dir[:dir]")
      "search for libraries in dir[:dir]"
  , Option "i"  ["import-dir"]
      (ReqArg (withArg onOpts $ \ arg opts -> opts { optImportPaths =
        nub $ optImportPaths opts ++
              map (normalise . addTrailingPathSeparator) (splitSearchPath arg)
              }) "dir[:dir]")
      "search for imports in dir[:dir]"
  , Option "o"  ["outdir"]
      (ReqArg (withArg onOpts $ \ arg opts -> opts { optOutDir = arg }) "dir")
      "write compilation artifacts (FlatCurry, ...) into directory `dir'"
  , Option []   ["htmldir"]
      (ReqArg (withArg onOpts $ \ arg opts -> opts { optHtmlDir =
        Just arg }) "dir")
      "write HTML documentation into directory `dir'"
  , Option ""   ["no-outdir", "no-subdir"]
      (NoArg (onOpts $ \ opts -> opts { optUseOutDir = False }))
      ("disable writing to `" ++ defaultOutDir ++ "' subdirectory")
  , Option ""   ["no-intf"]
      (NoArg (onOpts $ \ opts -> opts { optInterface = False }))
      "do not create an interface file"
    -- legacy warning flags
  , Option ""   ["no-warn"]
      (NoArg (onWarnOpts $ \ opts -> opts { wnWarn = False }))
      "do not print warnings"
  , Option ""   ["no-overlap-warn"]
      (NoArg (onWarnOpts $ \ opts -> opts {wnWarnFlags =
        addFlag WarnOverlapping (wnWarnFlags opts) }))
      "do not print warnings for overlapping rules"
  -- interfaces
  , Option ""   ["origin-pragmas"]
      (NoArg (onOpts $ \ opts -> opts { optOriginPragmas = True }))
      "emit origin pragmas in interfaces"
  -- target types
  , targetOption Tokens                 "tokens"
      "generate token stream"
  , targetOption Comments               "comments"
      "generate comments stream"
  , targetOption Parsed                 "parse-only"
      "generate source representation"
  , targetOption FlatCurry              "flat"
      "generate FlatCurry code"
  , targetOption TypedFlatCurry         "typed-flat"
      "generate typed FlatCurry code"
  , targetOption AnnotatedFlatCurry     "type-annotated-flat"
      "generate type-annotated FlatCurry code"
  , targetOption AbstractCurry          "acy"
      "generate typed AbstractCurry"
  , targetOption UntypedAbstractCurry   "uacy"
      "generate untyped AbstractCurry"
  , targetOption Html                   "html"
      "generate html documentation"
  , targetOption AST                    "ast"
      "generate abstract syntax tree"
  , targetOption ShortAST               "short-ast"
      "generate shortened abstract syntax tree for documentation"
  , Option "F"  []
      (NoArg (onPrepOpts $ \ opts -> opts { ppPreprocess = True }))
      "use custom preprocessor"
  , Option ""   ["pgmF"]
      (ReqArg (withArg onPrepOpts $ \ arg opts -> opts { ppCmd = arg})
        "cmd")
      "execute preprocessor command <cmd>"
  , Option ""   ["optF"]
      (ReqArg (withArg onPrepOpts $ \ arg opts ->
        opts { ppOpts = ppOpts opts ++ [arg]}) "option")
      "execute preprocessor with option <option>"
  -- extensions
  , Option "e"  ["extended"]
      (NoArg (onOpts id))
      "enable extended Curry functionalities (deprecated, enabled by default and kept for backwards compatibility)"
  , mkOptDescr onOpts      "c" ["case-mode"] "mode" "case mode"           caseModeDescriptions
  , mkOptDescr onOpts      "X" []            "ext"  "language extension"  extDescriptions
  , mkOptDescr onWarnOpts  "W" []            "opt"  "warning option"      warnDescriptions
  , mkOptDescr onDebugOpts "d" []            "opt"  "debug option"        debugDescriptions
  , mkOptDescr onOptimOpts "O" []            "opt"  "optimization option" optimizeDescriptions
  , Option ""   ["cpp"]
      (NoArg (onCppOpts $ \ opts -> opts { cppRun = True }))
      "run C preprocessor"
  , Option "D"  []
      (ReqArg (withArg ($) parseCppDefinition) "s=v")
      "define symbol `s` with value `v` for the C preprocessor"
  ]

parseCppDefinition :: String -> OptErr -> OptErr
parseCppDefinition arg optErr
  | not (null s) && not (null v) && all isDigit v
  = onCppOpts (addCppDefinition s v) optErr
  | otherwise
  = addErr (cppDefinitionErr arg) optErr
  where (s, v) = drop 1 <$> break ('=' ==) arg

addCppDefinition :: String -> String -> CppOpts -> CppOpts
addCppDefinition s v opts =
  opts { cppDefinitions = Map.insert s (read v) (cppDefinitions opts) }

cppDefinitionErr :: String -> String
cppDefinitionErr = (++) "Invalid format for option '-D': "

targetOption :: TargetType -> String -> String -> OptDescr (OptErr -> OptErr)
targetOption ty flag
  = Option "" [flag] (NoArg (onOpts $ \ opts -> opts { optTargetTypes =
      nub $ ty : optTargetTypes opts }))

verbDescriptions :: OptErrTable Options
verbDescriptions = map toDescr verbosities
  where
  toDescr (flag, name, desc)
    = (name, desc, \ opts -> opts { optVerbosity = flag })

extDescriptions :: OptErrTable Options
extDescriptions = map toDescr extensions
  where
  toDescr (flag, name, desc)
    = (name, desc,
        \opts -> let cppOpts = optCppOpts opts
                 in opts { optCppOpts    =
                             cppOpts { cppRun = cppRun cppOpts || flag == CPP }
                         , optExtensions = addFlag flag (optExtensions opts)
                         })


caseModeDescriptions :: OptErrTable Options
caseModeDescriptions
  = [ ( "curry"  , "use default curry case mode"
        , \ opts -> opts { optCaseMode = CaseModeCurry   } )
    , ( "free"   , "use free case mode"
        , \ opts -> opts { optCaseMode = CaseModeFree    } )
    , ( "haskell", "use haskell style case mode"
        , \ opts -> opts { optCaseMode = CaseModeHaskell } )
    , ( "prolog" , "use prolog style case mode"
        , \ opts -> opts { optCaseMode = CaseModeProlog  } )
    , ( "goedel"  , "use goedel case mode"
        , \ opts -> opts { optCaseMode = CaseModeGoedel  } )
    ]

warnDescriptions :: OptErrTable WarnOpts
warnDescriptions
  = [ ( "all"  , "turn on all warnings"
        , \ opts -> opts { wnWarnFlags = [minBound .. maxBound] } )
    , ("none" , "turn off all warnings"
        , \ opts -> opts { wnWarnFlags = []                     } )
    , ("error", "treat warnings as errors"
        , \ opts -> opts { wnWarnAsError = True                 } )
    ] ++ map turnOn warnFlags ++ map turnOff warnFlags
  where
  turnOn (flag, name, desc)
    = (name, "warn for " ++ desc
      , \ opts -> opts { wnWarnFlags = addFlag flag (wnWarnFlags opts)})
  turnOff (flag, name, desc)
    = ("no-" ++ name, "do not warn for " ++ desc
      , \ opts -> opts { wnWarnFlags = removeFlag flag (wnWarnFlags opts)})

debugDescriptions :: OptErrTable DebugOpts
debugDescriptions =
  [ ( "dump-all"          , "dump everything"
    , \ opts -> opts { dbDumpLevels = [minBound .. maxBound]    })
  , ( "dump-none"         , "dump nothing"
    , \ opts -> opts { dbDumpLevels = []                        })
  , ( "dump-env"          , "additionally dump compiler environment"
    , \ opts -> opts { dbDumpEnv = True                         })
  , ( "dump-raw"          , "dump as raw AST (instead of pretty printing)"
    , \ opts -> opts { dbDumpRaw = True                         })
  , ( "dump-all-bindings" , "when dumping bindings, dump all instead of just local ones"
    , \ opts -> opts { dbDumpAllBindings = True                 })
  , ( "dump-simple" , "print a simplified, more readable environment"
    , \ opts -> opts { dbDumpSimple = True                      })

  ] ++ map toDescr dumpLevel
  where
  toDescr (flag, name, desc)
    = (name , "dump code after " ++ desc
        , \ opts -> opts { dbDumpLevels = addFlag flag (dbDumpLevels opts)})

optimizeDescriptions :: OptErrTable OptimizationOpts
optimizeDescriptions =
  [ ( "desugar-newtypes"        , "desugars newtypes in FlatCurry"
    , \ opts -> opts { optDesugarNewtypes     = True    })
  , ( "inline-dictionaries"     , "inlines type class dictionaries"
    , \ opts -> opts { optInlineDictionaries  = True    })
  , ( "remove-unused-imports"   , "removes unused imports"
    , \ opts -> opts { optRemoveUnusedImports = True    })
  , ( "add-failed-case"         , "extends incomplete cases with explicit 'failed' in missing branches"
    , \ opts -> opts { optAddFailed           = True    })
  , ( "no-desugar-newtypes"     , "prevents desugaring of newtypes in FlatCurry"
    , \ opts -> opts { optDesugarNewtypes     = False   })
  , ( "no-inline-dictionaries"  , "prevents inlining of type class dictionaries"
    , \ opts -> opts { optInlineDictionaries  = False   })
  , ( "no-remove-unused-imports", "prevents removing of unused imports"
    , \ opts -> opts { optRemoveUnusedImports = False   })
  , ( "no-add-failed-case"         , "prevents extending incomplete cases with explicit 'failed' in missing branches"
    , \ opts -> opts { optAddFailed           = False    })
  ]

addFlag :: Eq a => a -> [a] -> [a]
addFlag o opts = nub $ o : opts

removeFlag :: Eq a => a -> [a] -> [a]
removeFlag o = filter (/= o)

-- |Update the 'Options' record by the parsed and processed arguments
updateOpts :: Options -> [String] -> (Options, [String], [String])
updateOpts opts args = (opts', files, errs ++ errs2 ++ checkOpts opts files)
  where
  (opts', errs2) = foldl (flip ($)) (opts, []) optErrs
  (optErrs, files, errs) = getOpt Permute options args

-- |Parse the command line arguments
parseOpts :: [String] -> (Options, [String], [String])
parseOpts = updateOpts defaultOptions

-- |Check options and files and return a list of error messages
checkOpts :: Options -> [String] -> [String]
checkOpts opts _
  = [ "The option '--htmldir' is only valid for HTML generation mode"
    | isJust (optHtmlDir opts) && Html `notElem` optTargetTypes opts ]

-- |Print the usage information of the command line tool.
usage :: String -> String
usage prog = usageInfo header options
  where header = "usage: " ++ prog ++ " [OPTION] ... MODULES ..."

-- |Retrieve the compiler 'Options'
getCompilerOpts :: IO (String, Options, [String], [String])
getCompilerOpts = do
  args <- getArgs
  prog <- getProgName
  let (opts, files, errs) = parseOpts args
  return (prog, opts, files, errs)
