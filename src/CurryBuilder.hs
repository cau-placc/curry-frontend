{- |
    Module      :  $Header$
    Description :  Build tool for compiling multiple Curry modules
    Copyright   :  (c) 2005        Martin Engelke
                       2007        Sebastian Fischer
                       2011 - 2015 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains functions to generate Curry representations for a
    Curry source file including all imported modules.
-}
module CurryBuilder (buildCurry, findCurry) where

import Control.Monad   (foldM, liftM)
import Data.Char       (isSpace)
import Data.Maybe      (catMaybes, fromMaybe, mapMaybe)
import System.FilePath ((</>), normalise)

import Curry.Base.Ident
import Curry.Base.Monad
import Curry.Base.Position (Position)
import Curry.Base.SpanInfo (spanInfo2Pos)
import Curry.Base.Pretty
import Curry.Files.Filenames
import Curry.Files.PathUtils
import Curry.Syntax ( ModulePragma (..), Extension (KnownExtension)
                    , KnownExtension (CPP), Tool (CYMAKE, FRONTEND) )

import Base.Messages

import CompilerOpts ( Options (..), CppOpts (..), DebugOpts (..)
                    , TargetType (..), defaultDebugOpts, updateOpts )
import CurryDeps    (Source (..), flatDeps)
import Modules      (compileModule)

-- |Compile the Curry module in the given source file including all imported
-- modules w.r.t. the given 'Options'.
buildCurry :: Options -> String -> CYIO ()
buildCurry opts s = do
  fn   <- findCurry opts s
  deps <- flatDeps  opts fn
  makeCurry opts' deps
  where
  opts' | null $ optTargetTypes opts = opts { optTargetTypes = [FlatCurry] }
        | otherwise                  = opts

-- |Search for a compilation target identified by the given 'String'.
findCurry :: Options -> String -> CYIO FilePath
findCurry opts s = do
  mbTarget <- findFile `orIfNotFound` findModule
  case mbTarget of
    Nothing -> failMessages [complaint]
    Just fn -> ok fn
  where
  canBeFile    = isCurryFilePath s
  canBeModule  = isValidModuleName s
  moduleFile   = moduleNameToFile $ fromModuleName s
  paths        = "." : optImportPaths opts
  findFile     = if canBeFile
                    then liftIO $ lookupCurryFile paths s
                    else return Nothing
  findModule   = if canBeModule
                    then liftIO $ lookupCurryFile paths moduleFile
                    else return Nothing
  complaint
    | canBeFile && canBeModule = errMissing "target" s
    | canBeFile                = errMissing "file"   s
    | canBeModule              = errMissing "module" s
    | otherwise                = errUnrecognized  s
  first `orIfNotFound` second = do
    mbFile <- first
    case mbFile of
      Nothing -> second
      justFn  -> return justFn

-- |Compiles the given source modules, which must be in topological order.
makeCurry :: Options -> [(ModuleIdent, Source)] ->  CYIO ()
makeCurry opts srcs = mapM_ process' (zip [1 ..] srcs)
  where
  total    = length srcs
  tgtDir m = addCurrySubdirModule (optUseSubdir opts) m

  process' :: (Int, (ModuleIdent, Source)) -> CYIO ()
  process' (n, (m, Source fn ps is)) = do
    opts' <- processPragmas opts ps
    process (adjustOptions (n == total) opts') (n, total) m fn deps
    where
    deps = fn : mapMaybe curryInterface is

    curryInterface i = case lookup i srcs of
      Just (Source    fn' _ _) -> Just $ tgtDir i $ interfName fn'
      Just (Interface fn'    ) -> Just $ tgtDir i $ interfName fn'
      _                        -> Nothing

  process' _ = return ()

adjustOptions :: Bool -> Options -> Options
adjustOptions final opts
  | final      = opts { optForce = optForce opts || isDump }
  | otherwise  = opts { optForce       = False
                      , optDebugOpts   = defaultDebugOpts
                      }
  where
  isDump = not $ null $ dbDumpLevels $ optDebugOpts opts


processPragmas :: Options -> [ModulePragma] -> CYIO Options
processPragmas opts0 ps = do
  let opts1 = foldl processLanguagePragma opts0
                [ e | LanguagePragma _ es <- ps, KnownExtension _ e <- es ]
  foldM processOptionPragma opts1 $
    [ (spanInfo2Pos p, s) | OptionsPragma p (Just FRONTEND) s <- ps ] ++
      [ (spanInfo2Pos p, s) | OptionsPragma p (Just CYMAKE) s <- ps ]
  where
  processLanguagePragma opts CPP
    = opts { optCppOpts = (optCppOpts opts) { cppRun = True } }
  processLanguagePragma opts _
    = opts
  processOptionPragma opts (p, s)
    | not (null unknownFlags)
    = failMessages [errUnknownOptions p unknownFlags]
    | optMode         opts /= optMode         opts'
    = failMessages [errIllegalOption p "Cannot change mode"]
    | optLibraryPaths opts /= optLibraryPaths opts'
    = failMessages [errIllegalOption p "Cannot change library path"]
    | optImportPaths  opts /= optImportPaths  opts'
    = failMessages [errIllegalOption p "Cannot change import path"]
    | optTargetTypes  opts /= optTargetTypes  opts'
    = failMessages [errIllegalOption p "Cannot change target type"]
    | otherwise
    = return opts'
    where
    (opts', files, errs) = updateOpts opts (quotedWords s)
    unknownFlags = files ++ errs

quotedWords :: String -> [String]
quotedWords str = case dropWhile isSpace str of
  []        -> []
  s@('\'' : cs) -> case break (== '\'') cs of
    (_     , []      ) -> def s
    (quoted, (_:rest)) -> quoted : quotedWords rest
  s@('"'  : cs) -> case break (== '"') cs of
    (_     , []      ) -> def s
    (quoted, (_:rest)) -> quoted : quotedWords rest
  s         -> def s
  where
  def s = let (w, rest) = break isSpace s in  w : quotedWords rest

-- |Compile a single source module.
process :: Options -> (Int, Int)
        -> ModuleIdent -> FilePath -> [FilePath] -> CYIO ()
process opts idx m fn deps
  | optForce opts = compile
  | otherwise     = smake (tgtDir (interfName fn) : destFiles) deps compile skip
  where
  skip    = status opts $ compMessage idx "Skipping" m (fn, head destFiles)
  compile = do
    status opts $ compMessage idx "Compiling" m (fn, head destFiles)
    compileModule opts m fn

  tgtDir = addCurrySubdirModule (optUseSubdir opts) m

  destFiles = [ gen fn | (t, gen) <- nameGens, t `elem` optTargetTypes opts]
  nameGens  =
    [ (Tokens              , tgtDir . tokensName       )
    , (Comments            , tgtDir . commentsName)
    , (Parsed              , tgtDir . sourceRepName    )
    , (FlatCurry           , tgtDir . flatName         )
    , (TypedFlatCurry      , tgtDir . typedFlatName    )
    , (AbstractCurry       , tgtDir . acyName          )
    , (UntypedAbstractCurry, tgtDir . uacyName         )
    , (AST                 , tgtDir . astName          )
    , (ShortAST            , tgtDir . shortASTName     )
    , (Html                , const (fromMaybe "." (optHtmlDir opts) </> htmlName m))
    ]

-- |Create a status message like
-- @[m of n] Compiling Module          ( M.curry, .curry/M.fcy )@
compMessage :: (Int, Int) -> String -> ModuleIdent
            -> (FilePath, FilePath) -> String
compMessage (curNum, maxNum) what m (src, dst)
  =  '[' : lpad (length sMaxNum) (show curNum) ++ " of " ++ sMaxNum  ++ "]"
  ++ ' ' : rpad 9 what ++ ' ' : rpad 16 (moduleName m)
  ++ " ( " ++ normalise src ++ ", " ++ normalise dst ++ " )"
  where
  sMaxNum  = show maxNum
  lpad n s = replicate (n - length s) ' ' ++ s
  rpad n s = s ++ replicate (n - length s) ' '

-- |A simple make function
smake :: [FilePath] -- ^ destination files
      -> [FilePath] -- ^ dependency files
      -> CYIO a     -- ^ action to perform if depedency files are newer
      -> CYIO a     -- ^ action to perform if destination files are newer
      -> CYIO a
smake dests deps actOutdated actUpToDate = do
  destTimes <- catMaybes `liftM` mapM (liftIO . getModuleModTime) dests
  depTimes  <- mapM (cancelMissing getModuleModTime) deps
  make destTimes depTimes
  where
  make destTimes depTimes
    | length destTimes < length dests = actOutdated
    | outOfDate destTimes depTimes    = actOutdated
    | otherwise                       = actUpToDate

  outOfDate tgtimes dptimes = or [ tg < dp | tg <- tgtimes, dp <- dptimes]

cancelMissing :: (FilePath -> IO (Maybe a)) -> FilePath -> CYIO a
cancelMissing act f = liftIO (act f) >>= \res -> case res of
  Nothing  -> failMessages [errModificationTime f]
  Just val -> ok val

errUnknownOptions :: Position -> [String] -> Message
errUnknownOptions p errs = posMessage p $
  text "Unknown flag(s) in {-# OPTIONS_FRONTEND #-} pragma:"
  <+> sep (punctuate comma $ map text errs)

errIllegalOption :: Position -> String -> Message
errIllegalOption p err = posMessage p $
  text "Illegal option in {-# OPTIONS_FRONTEND #-} pragma:" <+> text err

errMissing :: String -> String -> Message
errMissing what which = message $ sep $ map text
  [ "Missing", what, quote which ]

errUnrecognized :: String -> Message
errUnrecognized f = message $ sep $ map text
  [ "Unrecognized input", quote f ]

errModificationTime :: FilePath -> Message
errModificationTime f = message $ sep $ map text
  [ "Could not inspect modification time of file", quote f ]

quote :: String -> String
quote s = "\"" ++ s ++ "\""
