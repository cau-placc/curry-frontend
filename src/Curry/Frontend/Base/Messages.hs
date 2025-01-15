{- |
    Module      :  $Header$
    Description :  Construction and output of compiler messages
    Copyright   :  (c) 2011 - 2016 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines several operations to construct and emit compiler
    messages to the user.
-}
module Curry.Frontend.Base.Messages
  ( -- * Output of user information
    MonadIO (..), status, putMsg, putErrLn, putErrsLn
    -- * program abortion
  , abortWith, abortWithMessage, abortWithMessages, warnOrAbort, internalError
    -- * creating messages
  , Message, message, posMessage, spanInfoMessage
  ) where

import Control.Monad              (unless, when)
import Control.Monad.IO.Class     (MonadIO(..))
import Data.List                  (sort)
import GHC.Stack                  (HasCallStack)
import System.IO                  (hFlush, hPutStrLn, stderr, stdout)
import System.Exit                (exitFailure)

import Curry.Base.Message         ( Message, message, posMessage, spanInfoMessage
                                  , ppWarning, ppMessagesWithPreviews, ppError)
import Curry.Base.Pretty          (Doc, text)
import Curry.Frontend.CompilerOpts               (Options (..), WarnOpts (..), Verbosity (..))

-- |Print a status message, depending on the current verbosity
status :: MonadIO m => Options -> String -> m ()
status opts msg = unless (optVerbosity opts < VerbStatus) (putMsg msg)

-- |Print a message on 'stdout'
putMsg :: MonadIO m => String -> m ()
putMsg msg = liftIO (putStrLn msg >> hFlush stdout)

-- |Print an error message on 'stderr'
putErrLn :: MonadIO m => String -> m ()
putErrLn msg = liftIO (hPutStrLn stderr msg >> hFlush stderr)

-- |Print a list of error messages on 'stderr'
putErrsLn :: MonadIO m => [String] -> m ()
putErrsLn = mapM_ putErrLn

-- |Print a list of 'String's as error messages on 'stderr'
-- and abort the program
abortWith :: [String] -> IO a
abortWith errs = putErrsLn errs >> exitFailure

-- |Print a single error message on 'stderr' and abort the program
abortWithMessage :: Message -> IO a
abortWithMessage msg = abortWithMessages [msg]

-- |Print a list of error messages on 'stderr' and abort the program
abortWithMessages :: [Message] -> IO a
abortWithMessages msgs = printMessages ppError msgs >> exitFailure

-- |Print a list of warning messages on 'stderr' and abort the program
--  if the -Werror command-line option is set.
--
--  Note that module-level checks are encouraged to emit warnings via
--  `warnOrFailMessages`, which handles -Werror at the emission site. These
--  warnings may thus already show up as errors once they reach this function.
--  The motivation for checking -Werror again in this function is to provide a
--  fallback for warnings emitted in non-options-aware contexts, e.g. the lexer.
warnOrAbort :: WarnOpts -> [Message] -> IO ()
warnOrAbort opts msgs = when (wnWarn opts && not (null msgs)) $ do
  if wnWarnAsError opts
    then abortWithMessages (msgs ++ [message $ text "Failed due to top-level -Werror"])
    else printMessages ppWarning msgs

-- |Print a list of messages on 'stderr'
printMessages :: (Message -> Doc) -> [Message] -> IO ()
printMessages msgType msgs
  = unless (null msgs) (putErrLn . show =<< ppMessagesWithPreviews msgType (sort msgs))

-- |Raise an internal error
internalError :: HasCallStack => String -> a
internalError msg = error $ "Internal error: " ++ msg
