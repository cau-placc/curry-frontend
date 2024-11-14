{- |
    Module      :  $Header$
    Description :  Main module
    Copyright   :  (c) 2005        Martin Engelke
                       2011 - 2016 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Command line tool for generating Curry representations (e.g. FlatCurry,
    AbstractCurry) for a Curry source file including all imported modules.
-}
module Main (main) where

import Curry.Base.Monad (runCYIO)

import Curry.Frontend.Base.Messages
import Curry.Frontend.Files.FrontendPath (frontendGreeting, frontendVersion)

import Curry.Frontend.CurryBuilder       (buildCurry)
import Curry.Frontend.CompilerOpts       (Options (..), FrontendMode (..), getCompilerOpts, usage)

-- |The command line tool frontend
main :: IO ()
main = getCompilerOpts >>= runFrontend

-- |Invoke the curry frontend w.r.t the command line arguments
runFrontend :: (String, Options, [String], [String]) -> IO ()
runFrontend (prog, opts, files, errs) = case optMode opts of
  ModeHelp             -> printUsage prog
  ModeVersion          -> printVersion
  ModeNumericVersion   -> printNumericVersion
  ModeMake | not (null errs) -> badUsage prog errs
           | null files      -> badUsage prog ["No input files"]
           | otherwise       -> runCYIO (mapM_ (buildCurry opts) files) >>=
                                either abortWithMessages continueWithMessages
  where continueWithMessages = warnOrAbort (optWarnOpts opts) . snd

-- |Print the usage information of the command line tool
printUsage :: String -> IO ()
printUsage prog = putStrLn $ usage prog

-- |Print the program version
printVersion :: IO ()
printVersion = putStrLn frontendGreeting

-- |Print the numeric program version
printNumericVersion :: IO ()
printNumericVersion = putStrLn frontendVersion

-- |Print errors and abort execution on bad parameters
badUsage :: String -> [String] -> IO ()
badUsage prog errs = do
  putErrsLn $ map (\ err -> prog ++ ": " ++ err) errs
  abortWith ["Try '" ++ prog ++ " --help' for more information"]
