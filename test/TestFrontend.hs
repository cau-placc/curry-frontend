--------------------------------------------------------------------------------
-- Test Suite for the Curry Frontend
--------------------------------------------------------------------------------
--
-- This Test Suite supports three kinds of tests:
--
-- 1) tests which should pass
-- 2) tests which should pass with a specific warning
-- 3) tests which should fail yielding a specific error message
--
-- In order to add a test to this suite, proceed as follows:
--
-- 1) Store your test code in a file (please use descriptive names) and put it
--    in the corresponding subfolder (i.e. test/pass for passing tests,
--    test/fail for failing tests and test/warning for passing tests producing
--    warnings)
-- 2) Extend the corresponding test information list (there is one for each test
--    group at the end of this file) with the required information (i.e. name of
--    the Curry module to be tested and expected warning/failure message(s))
-- 3) Run 'cabal test'
module TestFrontend (tests) where

import qualified Control.Exception as E (SomeException, catch)

import           Data.Either            (fromLeft)
import           Data.List              (isInfixOf, sort)
import qualified Data.Map as Map        (insert)
import           Data.Maybe             (fromMaybe)
import           Distribution.TestSuite ( Test (..), TestInstance (..)
                                        , Progress (..), Result (..)
                                        , OptionDescr)
import           System.FilePath        ((</>), (<.>))
import           System.Directory       (removePathForcibly)

import           Curry.Base.Message     (Message, message, ppMessages, ppError)
import           Curry.Base.Monad       (CYIO, runCYIO)
import           Curry.Base.Pretty      (text, render)

import qualified Curry.Frontend.CompilerOpts as CO ( Options (..), WarnOpts (..)
                                                   , WarnFlag (..), Verbosity (VerbQuiet)
                                                   , CppOpts (..)
                                                   , defaultOptions )
import           Curry.Frontend.CurryBuilder       ( buildCurry )

tests :: IO [Test]
tests = do
  removePathForcibly "test/fail/.curry"
  removePathForcibly "test/pass/.curry"
  removePathForcibly "test/warning/.curry"
  return [failingTests, passingTests, warningTests]

runSecure :: CYIO a -> IO (Either [Message] a, [Message])
runSecure act = runCYIO act `E.catch` handler
  where handler e = return (Left [message $ text $ show (e :: E.SomeException)], [])

-- Execute a test by calling the frontend
runTest :: CO.Options -> String -> [String] -> IO Progress
runTest opts test errorMsgs =
  if null errorMsgs
    then passOrFail <$> runSecure (buildCurry opts' test)
    else catchE     <$> runSecure (buildCurry opts' test)
  where
    cppOpts        = CO.optCppOpts opts
    cppDefs        = Map.insert "__PAKCS__" 3 (CO.cppDefinitions cppOpts)
    wOpts          = CO.optWarnOpts opts
    wFlags         =   CO.WarnUnusedBindings
                     : CO.WarnUnusedGlobalBindings
                     : CO.WarnImportNameShadowing
                     : CO.wnWarnFlags wOpts
    opts'          = opts { CO.optForce    = True
                          , CO.optWarnOpts = wOpts
                             { CO.wnWarnFlags    = wFlags  }
                          , CO.optCppOpts  = cppOpts
                             { CO.cppDefinitions = cppDefs }
                          }
    passOrFail     = Finished . either failAct (const Pass) . fst
    catchE (e, ws) = Finished . passAct $ fromLeft [] e ++ ws
    failAct msgs
      | null msgs  = Pass
      | otherwise  = Fail $ "An unexpected failure occurred: " ++
                            showMessages msgs
    passAct msgs
      | null otherMsgs = Pass
      | otherwise      = Fail $ "Expected warnings/failures did not occur: " ++
                                unwords otherMsgs
      where
        errorStr  = showMessages msgs
        otherMsgs = filter (not . flip isInfixOf errorStr) errorMsgs

showMessages :: [Message] -> String
showMessages = render . ppMessages ppError . sort

-- group of test which should fail yielding a specific error message
failingTests :: Test
failingTests = Group { groupName    = "Failing Tests"
                     , concurrently = False
                     , groupTests   = map (mkTest "test/fail/") failInfos
                     }

-- group of tests which should pass
passingTests :: Test
passingTests = Group { groupName    = "Passing Tests"
                     , concurrently = False
                     , groupTests   = map (mkTest "test/pass/") passInfos
                     }

-- group of tests which should pass producing a specific warning message
warningTests :: Test
warningTests = Group { groupName    = "Warning Tests"
                     , concurrently = False
                     , groupTests   = map (mkTest "test/warning/") warnInfos
                     }

-- create a new test
mkTest :: FilePath -> TestInfo -> Test
mkTest path (testName, testTags, testOpts, mSetOpts, errorMsgs, litFile) =
  let file = path </> testName <.> if litFile then "lcurry" else "curry"
      opts = CO.defaultOptions { CO.optVerbosity   = CO.VerbQuiet
                               , CO.optImportPaths = [path]
                               }
      test = TestInstance
        { run       = runTest opts file errorMsgs
        , name      = testName
        , tags      = testTags
        , options   = testOpts
        , setOption = fromMaybe (\_ _ -> Right test) mSetOpts
        }
  in Test test

-- Information for a test instance:
-- * name of test
-- * tags to classify a test
-- * options
-- * function to set options
-- * optional warning/error message which should be thrown on execution of test
-- * literate file
type TestInfo = (String, [String], [OptionDescr], Maybe SetOption, [String], Bool)

type SetOption = String -> String -> Either String TestInstance

--------------------------------------------------------------------------------
-- Definition of failing tests
--------------------------------------------------------------------------------

-- generate a simple failing test
mkFailTest :: String -> [String] -> TestInfo
mkFailTest nm errorMsgs = (nm, [], [], Nothing, errorMsgs, False)

-- To add a failing test to the test suite simply add the module name of the
-- test code and the expected error message(s) to the following list
failInfos :: [TestInfo]
failInfos = map (uncurry mkFailTest)
  [ ("CaseModeH",
      [ "Symbol `B' is a variable name, but the selected case mode is `haskell`, try renaming to b instead"
      , "Symbol `B' is a variable name, but the selected case mode is `haskell`, try renaming to b instead"
      , "Symbol `Xs' is a variable name, but the selected case mode is `haskell`, try renaming to xs instead"
      , "Symbol `c' is a data declaration name, but the selected case mode is `haskell`, try renaming to C instead"
      , "Symbol `f' is a constructor name, but the selected case mode is `haskell`, try renaming to F instead"
      ]
    )
  , ("CaseModeP",
      [ "Symbol `a' is a variable name, but the selected case mode is `prolog`, try renaming to A instead"
      , "Symbol `a' is a variable name, but the selected case mode is `prolog`, try renaming to A instead"
      , "Symbol `mf' is a variable name, but the selected case mode is `prolog`, try renaming to Mf instead"
      , "Symbol `E' is a constructor name, but the selected case mode is `prolog`, try renaming to e instead"
      ]
    )
  , ("CyclicImports/A", ["Cyclic import dependency"])
  , ("CyclicImports/B", ["Cyclic import dependency"])
  , ("DataFail",
      [ "Missing instance for Prelude.Data Test1"
      , "Missing instance for Prelude.Data (Test2"
      , "Missing instance for Prelude.Data (Test2"
      , "Missing instance for Prelude.Data Test1"
      ]
    )
  , ("ErrorMultipleSignature", ["More than one type signature for `f'"])
  , ("ErrorMultipleSignature", ["More than one type signature for `f'"])
  , ("ExportCheck/AmbiguousName", ["Ambiguous name `not'"])
  , ("ExportCheck/AmbiguousType", ["Ambiguous type `Bool'"])
  , ("ExportCheck/ModuleNotImported", ["Module `Foo' not imported"])
  , ("ExportCheck/MultipleName", ["Multiple exports of name `not'"])
  , ("ExportCheck/MultipleType", ["Multiple exports of type `Bool'"])
  , ("ExportCheck/NoDataType", ["`Foo' is not a data type"])
  , ("ExportCheck/OutsideTypeConstructor", ["Data constructor `False' outside type export in export list"])
  , ("ExportCheck/OutsideTypeLabel", ["Label `value' outside type export in export list"])
  , ("ExportCheck/UndefinedElement", ["`foo' is not a constructor or label of type `Bool'"])
  , ("ExportCheck/UndefinedName", ["Undefined name `foo' in export list"])
  , ("ExportCheck/UndefinedType", ["Undefined type or class `Foo' in export list"])
  , ("FD_TestSpec",
      [ "Missing instance for Test Prelude.Bool Prelude.Int"
      , "arising from variable"
      , "use"
      ]
    )
  , ("FD_TypeError2",
      ["Missing instance for Collects Prelude.Bool"
      , "arising from variable"
      , "insert"
      ]
    )
  , ("FP_Cyclic", ["Function `g' used in functional pattern depends on `f'  causing a cyclic dependency"])
  , ("FP_Restrictions",
      [ "Functional patterns are not supported inside a case expression"
      , "Functional patterns are not supported inside a case expression"
      , "Functional patterns are not supported inside a list comprehension"
      , "Functional patterns are not supported inside a do sequence"
      ]
    )
  , ("HaskellRecordsFail", ["Unexpected token `,'"])
  , ("FP_NonGlobal", ["Function `f1' in functional pattern is not global"])
  , ("ImportError",
      [ "Module Prelude does not export foo"
      , "Module Prelude does not export bar"
      ]
    )
  , ("KindCheck",
      [ "Type variable a occurs more than once in left hand side of type declaration"
      , "Type variable b occurs more than once in left hand side of type declaration"
      ]
    )
  , ("MissingLabelInUpdate",
      ["Undefined record label `l1'"] )
  , ("MPTC_BoundVar",
      ["Unbound type variable b"]
    )
  , ("MPTC_BoundVar2",
      ["Unbound type variable b"]
    )
  , ("MPTC_CovCond",
      ["MPTC_CovCond"
      , "Violation of a functional dependency in instance declaration for"
      , "Mult a [b] [c]"
      , "The left-hand side instance type types a [b]"
      , "do not uniquely determine the right-hand side instance type type [c]"
      , "because the type variable `c' does not occur in the former."
      ]
    )
  , ("MPTCAmbiguousTypeVar",
      -- Many parts in these error message are left out due to possible variable
      -- name changes. Example of an actual error message:
      --   Ambiguous type variable _8
      --   in type (C _8 _6, C _7 _8) => _7 -> _6
      --   inferred for function `f1'
      [ "Ambiguous type variable" , "inferred for function `f1'"
      , "inferred for function `f2'"
      ]
    )
  , ("MPTCDeriving",
      [ "The type constraint C a a is not smaller"
      , "than the head of the derived instance", "Prelude.Eq (T1 a)"
      , "The type variable `a' occurs more often", "in the constraint C a a"
      , "than in the head of the derived instance" -- Prelude.Eq (T1 a)
      , "Missing instance for C [a] [b]", "in derived instance for"
      , "Prelude.Eq (T2 a b)"
      , "Instance overlap for C (a, b) (b, b)"
      , "arising in derived instance", "Prelude.Show (T3 a b)"
      , "Matching instances:", "C (a, b) (b, c) (defined in MPTCDeriving)"
      , "C (a, b) (c, b) (defined in MPTCDeriving)"
      ]
    )
  , ("MPTCFlexibleContext",
      [ "Constraint with non-variable argument C Prelude.Bool" -- C Prelude.Bool a
      , "occurring in the context of the inferred type for function declaration `f1'"
      , "Type error in application", "f3a (1 :: Int)"
      , "Types Prelude.Bool and Prelude.Int are incompatible"
      ]
    )
  , ("MPTCInstanceOverlap",
      -- The following error messages expected for this module explicitly
      -- include source span data, since that is partly the only part of the
      -- messages that differentiates them.
      [ "MPTCInstanceOverlap.curry:14:6-14:12 Error:"
      , "Instance overlap for C [Prelude.Bool] [Prelude.Bool] [Prelude.Bool]"
      , "arising from variable", "methodC"
      , "Matching instances:", "C [a] [a] [b] from MPTCInstanceOverlap"
      , "C [a] [b] [b] from MPTCInstanceOverlap"
      , "MPTCInstanceOverlap.curry:17:12-17:18 Error:"
      , "MPTCInstanceOverlap.curry:25:19-25:25 Error:"
      , "MPTCInstanceOverlap.curry:29:11-29:12 Error:", "f'"
      ]
    )
  , ("MPTCInstanceTermination",
      [ "The type variable `b' occurs more often"
      , "in the constraint C b b", "than in the instance head C [b] Bool"
      , "The type constraint C a a is not smaller", "than the instance head D [a]"
      ]
    )
  , ("MPTCInvalidMethodType",
        -- methodC1 :: a -> c -> a
      [ "Method type does not uniquely determine class variable `b'"
        -- methodC2 :: Eq b => a -> b -> c
      , "Constraint Eq b", "in method context constrains only class variables"
        -- methodC3 :: D b c a b => a -> b -> c
      , "Constraint D b c a b" -- "in method context constrains only class variables"
      ]
    )
  , ("MPTCMissingInstance",
      [ "Missing instance for C Prelude.Bool [Prelude.Bool]" -- f1 = methodC True [True]
      , "arising from variable", "methodC"
      , "Missing instance for D", {- arising from variable -} "methodD" -- f2 = methodD
      ]
    )
  , ("MPTCMissingSuperClassInstance",
      [ "Missing instance for C Prelude.Int Prelude.Bool"
      , "in instance declaration for"
      , "D Prelude.Bool Prelude.Int"
      , "Missing instance for C (b, a) (a, b)"
      , "in instance declaration for"
      , "D (a, b) (b, a)"
      , "Instance overlap for C (a, b) (a, b)"
      , "arising in instance declaration", "D (a, b) (a, b)"
      , "Matching instances:"
      , "C (a, b) (a, c) (defined in MPTCMissingSuperClassInstance)"
      , "C (a, b) (c, b) (defined in MPTCMissingSuperClassInstance)"
      , "Missing instance for D Prelude.Bool Prelude.Bool"
      , "in instance declaration for"
      , "F Prelude.Bool"
      , "Missing instance for E" -- "in instance declaration F Prelude.Bool"
      ]
    )
  , ("MPTCNoExtension",
      [ "Multi-parameter type class declaration C a b"
      , "Nullary type class declaration D"
      , "Multiple types in instance declaration C Bool Bool"
      , "Zero types in instance declaration D"
      ]
    )
  , ("MPTCSuperClassCycle",
      [ "Mutually recursive type classes C, D (line 7.18), and E (line 9.16)"
      , "Mutually recursive type classes F and G (line 13.12)"
      ]
    )
  , ("MPTCWrongClassArity",
      [ "Kind error in instance declaration", "instance C"
      , "The type class `C' has been applied to 0 types,"
      , "but it has 1 type parameter."
      , "Kind error in class constraint", "C a b"
      , "The type class `C' has been applied to 2 types," -- "but it has 1 type parameter."
      , {- Kind error in class constraint -} "D a"
      , "The type class `D' has been applied to 1 type,"
      , "but it has 2 type parameters."
      , {- Kind error in instance declaration -} "instance D Bool Bool Bool"
      , "The type class `D' has been applied to 3 types,"-- "but it has 2 type parameters."
      , {- Kind error in instance declaration -} "instance E Bool"
      , "The type class `E' has been applied to 1 type,"
      , "but it has 0 type parameters."
      ]
    )
  , ("MPTCWrongKind",
      [ "Kind error in instance declaration", "instance C Bool []"
      ,   "Type: Bool", "Inferred kind: *", "Expected kind: * -> *"
        {- "Kind error in instance declaration", "instance C Bool []" -}
      ,   "Type: []", "Inferred kind: * -> *", "Expected kind: *"
      , "Kind error in type expression", "a Bool"
      ,   "Type: a", "Kind: *", "Cannot be applied"
      , {- "Kind error in type expression" -} "a Bool -> b"
      ,   "Type: b" {- "Inferred kind: * -> *", "Expected kind: *" -}
      , "Kind error in class constraint", "C a a"
          {- "Type: a", "Inferred kind: * -> *", "Expected kind: *" -}
      , {- "Kind error in type expression" -} "b a"
      ,   {- "Type: a" -} "Inferred kind: (* -> *) -> *" {- "Expected kind: *" -}
      ]
    )
  , ("ClassHiddenFail",
      [ "`methodB' is not a (visible) method of class `A'",
        "`methodB' is undefined"])
  , ("ModuleLevelWerror",
      [ "Failed due to -Werror"
      , "Top-level binding with no type signature"
      ])
  , ("MultipleArities", ["Equations for `test' have different arities"])
  , ("MultipleInstances", ["Multiple instances for the same class and type"])
  , ("MultipleDefinitions",
      ["Multiple definitions for data/record constructor `Rec'"]
    )
  , ("MultiplePrecedence",
      ["More than one fixity declaration for `f'"]
    )
  , ("PatternRestrictions",
      [ "Lazy patterns are not supported inside a functional pattern"]
    )
  , ("PragmaError", ["Unknown language extension"])
  , ("PrecedenceRange", ["Precedence out of range"])
  , ("RecordLabelIDs", ["Multiple declarations of `RecordLabelIDs.id'"])
  , ("RecursiveImport", ["Recursive import for module Recursive"])
  , ("RecursiveTypeSyn", ["Mutually recursive synonym and/or renaming types A and B (line 12.6)"])
  , ("SyntaxError", ["Type error in application"])
  , ("TypedFreeVariables",
      ["Variable x has a polymorphic type", "Type error in function definition"]
    )
  , ("TypeError1", ["Type error in explicitly typed expression"])
  , ("TypeError2", ["Missing instance for Prelude.Num Prelude.Bool"])
  , ("TypeSigTooGeneral",
      [ "Type signature too general"
      , "Function: h"
      , "Type signature too general"
      , "Function: g'"
      , "Type signature too general"
      , "Function: n"
      ]
    )
  , ("UnboundTypeVariable",
      [ "Unbound type variable b"
      , "Unbound type variable c"
      ]
    )
  ]

--------------------------------------------------------------------------------
-- Definition of passing tests
--------------------------------------------------------------------------------

-- generate a simple passing test
mkPassTest :: String -> TestInfo
mkPassTest = flip mkFailTest []

-- generate a simple passing test for literate files
mkPassLitTest :: String -> TestInfo
mkPassLitTest nm = (nm, [], [], Nothing, [], True)

-- To add a passing test to the test suite simply add the module name of the
-- test code to the following list
passInfos :: [TestInfo]
passInfos = map mkPassTest
  [ "AbstractCurryBug"
  , "ACVisibility"
  , "AnonymVar"
  , "CaseComplete"
  , "CaseModeTypeVarDisambiguation"
  , "DataPass"
  , "DefaultPrecedence"
  , "Dequeue"
  , "EmptyWhere"
  , "ExplicitLayout"
  , "FCase"
  , "FD_ListLike"
  , "FD_ListLike2"
  , "FlexC_ListLike"
  , "FlexI_ListLike"
  , "FlexI_ListLike2"
  , "FP_Lifting"
  , "FP_NonCyclic"
  , "FP_NonLinearity"
  , "FunctionalPatterns"
  , "FunDepExample"
  , "HaskellRecords"
  , "FunDepImpliesMPTC"
  , "HaskellRecordsPass"
  , "Hierarchical"
  , "ImportRestricted"
  , "ImportRestricted2"
  , "InstanceExport"
  , "Infix"
  , "Inline"
  , "Lambda"
  , "List"
  , "Maybe"
  , "MPTCCoercible"
  , "MPTCConstrainedMethods"
  , "MPTCDefaultMethodImpls"
  , "MPTCDeriving"
  , "MPTCNoExtension"
  , "MPTCNullary"
  , "MPTCNullaryClasses"
  , "MPTCPotentialInstanceOverlap"
  , "MPTCSuperClasses"
  , "NegLit"
  , "Newtype1"
  , "Newtype2"
  , "NonLinearLHS"
  , "OperatorDefinition"
  , "OverloadedLocal"
  , "PatDecl"
  , "Prelude"
  , "Pretty"
  , "RecordsPolymorphism"
  , "RecordTest1"
  , "RecordTest2"
  , "RecordTest3"
  , "ReexportTest"
  , "SelfExport"
  , "SpaceLeak"
  , "TyConsTest"
  , "TypedExpr"
  , "UntypedAcy"
  , "Unzip"
  , "WhereAfterDo"
  ] ++ map mkPassLitTest
  [ "LiterateImport"
  ]

--------------------------------------------------------------------------------
-- Definition of warning tests
--------------------------------------------------------------------------------

-- To add a warning test to the test suite simply add the module name of the
-- test code and the expected warning message(s) to the following list
warnInfos :: [TestInfo]
warnInfos = map (uncurry mkFailTest)
  [
    ("AliasClash",
      [ "The module alias `AliasClash' overlaps with the current module name"
      , "Overlapping module aliases"
      , "Module List is imported more than once"
      ]
    )
  , ("Case1", ["Pattern matches are non-exhaustive", "In an equation for `h'"])
  , ("Case2",
      [ "An fcase expression is potentially non-deterministic due to overlapping rules"
      , "Pattern matches are non-exhaustive", "In an fcase alternative"
      , "In a case alternative", "In an equation for `fp'"
      , "Pattern matches are potentially unreachable"
      , "Function `fp' is potentially non-deterministic due to overlapping rules"
      , "Pattern matches are non-exhaustive"
      ]
    )
  , ("CaseModeC",
      [ "Symbol `B' is a variable name, but the selected case mode is `curry`, try renaming to b instead"
      , "Symbol `B' is a variable name, but the selected case mode is `curry`, try renaming to b instead"
      , "Symbol `Xs' is a variable name, but the selected case mode is `curry`, try renaming to xs instead"
      , "Symbol `c' is a data declaration name, but the selected case mode is `curry`, try renaming to C instead"
      , "Symbol `f' is a constructor name, but the selected case mode is `curry`, try renaming to F instead"
      ]
    )
  , ("CheckSignature",
      [ "Top-level binding with no type signature: hw"
      , "Top-level binding with no type signature: f"
      , "Unused declaration of variable `answer'"
      ]
    )
  , ("MissingFields",
      [ "Fields of `P' not initialized and implicitly free: w"
      , "Fields of `N' not initialized and implicitly free: unN"
      ]
    )
  , ("MissingTypeImportAsVariable",
      [ "Symbol `IORef' is a variable name, but the selected case mode is `curry`, try renaming to iORef instead"
      ]
    )
  , ("MPTCIncompleteInstance",
      [ "No explicit implementation for method `methodC3'"
      , "No explicit implementation for method `methodD1'"
      , "No explicit implementation for method `methodD2'"
      ]
    )
  , ("MPTCOrphanInstance",
      [ "Orphan instance: instance C Foo Bool"
      , "Orphan instance: instance E"
      ]
    )
  , ("MPTCUniqelyButNoInstance",
      [ "Top-level binding with no type signature:"
      , "  test :: Coerce Prelude.Char"
      ])
  , ("NonExhaustivePattern",
      [ "Pattern matches are non-exhaustive", "In a case alternative"
      , "In an equation for `test2'", "In an equation for `and'"
      , "In an equation for `plus'", "In an equation for `len2'"
      , "In an equation for `tuple'", "In an equation for `tuple2'"
      , "In an equation for `g'", "In an equation for `rec'"]
    )
  , ("NoRedundant", [])
  , ("OverlappingPatterns",
      [ "Pattern matches are potentially unreachable", "In a case alternative"
      , "An fcase expression is potentially non-deterministic due to overlapping rules"
      , "Function `i' is potentially non-deterministic due to overlapping rules"
      , "Function `j' is potentially non-deterministic due to overlapping rules"
      , "Function `k' is potentially non-deterministic due to overlapping rules"
      ]
    )
  , ("QualRedundant",
      [ "Redundant context in type signature for function `f': 'P.Eq a'"]
    )
  , ("Redundant",
      [ "Redundant context in type signature for function `f': 'Eq a'"]
    )
  , ("ShadowingSymbols",
      [ "Unused declaration of variable `x'", "Shadowing symbol `x'"])
  , ("ShadowingImports",
      [ "Shadowing symbol `failed'", "Shadowing symbol `isAlpha'" ])
  , ("TabCharacter",
      [ "Tab character"])
  , ("UnexportedFunction",
      [ "Unused declaration of variable `q'"
      , "Unused declaration of variable `g'" ]
    )
  ]
