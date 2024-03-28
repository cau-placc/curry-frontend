{- |
    Module      :  $Header$
    Description :  Monads for message handling
    Copyright   :  2014 - 2016 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental

    The monads defined in this module provide a common way to stop execution
    when some errors occur. They are used to integrate different compiler passes
    smoothly.
-}

module Curry.Base.Monad
  ( CYIO, CYM, CYT, failMessages, failMessageAt, warnMessages, warnMessageAt, warnOrFailMessages
  , ok, runCYIO, runCYM, runCYIOIgnWarn, runCYMIgnWarn, liftCYM, silent
  ) where

import Control.Monad.Identity
import Control.Monad.Trans.Except (ExceptT, mapExceptT, runExceptT, throwE)
import Control.Monad.Writer
    ( MonadTrans(lift),
      WriterT(runWriterT),
      censor,
      mapWriterT,
      MonadWriter(tell) )

import Curry.Base.Message  (Message, spanMessage, message)
import Curry.Base.Span (Span)
import Curry.Base.Pretty   (text)
import CompilerOpts (WarnOpts (..))

-- |Curry compiler monad transformer
type CYT m a = WriterT [Message] (ExceptT [Message] m) a

-- |Curry compiler monad based on the `IO` monad
type CYIO a = CYT IO a

-- |Pure Curry compiler monad
type CYM a = CYT Identity a

-- |Run an `IO`-based Curry compiler action in the `IO` monad,
-- yielding either a list of errors or a result in case of success
-- consisting of the actual result and a (possibly empty) list of warnings
runCYIO :: CYIO a -> IO (Either [Message] (a, [Message]))
runCYIO = runExceptT . runWriterT

-- |Run an pure Curry compiler action,
-- yielding either a list of errors or a result in case of success
-- consisting of the actual result and a (possibly empty) list of warnings
runCYM :: CYM a -> Either [Message] (a, [Message])
runCYM = runIdentity . runExceptT . runWriterT

-- |Run an `IO`-based Curry compiler action in the `IO` monad,
-- yielding either a list of errors or a result in case of success.
runCYIOIgnWarn :: CYIO a -> IO (Either [Message] a)
runCYIOIgnWarn = runExceptT . (liftM fst) . runWriterT

-- |Run an pure Curry compiler action,
-- yielding either a list of errors or a result in case of success.
runCYMIgnWarn :: CYM a -> Either [Message] a
runCYMIgnWarn = runIdentity . runExceptT . (liftM fst) . runWriterT

-- |Failing action with a message describing the cause of failure.
failMessage :: Monad m => Message -> CYT m a
failMessage msg = failMessages [msg]

-- |Failing action with a list of messages describing the cause(s) of failure.
failMessages :: Monad m => [Message] -> CYT m a
failMessages = lift . throwE

-- |Failing action with a source code span and a `String` indicating
-- the cause of failure.
failMessageAt :: Monad m => Span -> String -> CYT m a
failMessageAt sp s = failMessage $ spanMessage sp $ text s

-- |Warning with a message describing the cause of the warning.
warnMessage :: Monad m => Message -> CYT m ()
warnMessage msg = warnMessages [msg]

-- |Warning with a list of messages describing the cause(s) of the warnings.
warnMessages :: Monad m => [Message] -> CYT m ()
warnMessages msgs = tell msgs

-- |Warnings or failures, depending on whether -Werror is set.
warnOrFailMessages :: Monad m => WarnOpts -> [Message] -> CYT m ()
warnOrFailMessages opts msgs | null msgs          = return ()
                             | wnWarnAsError opts = failMessages msgs
                             | otherwise          = warnMessages msgs

-- |Execute a monadic action, but ignore any warnings it issues
silent :: Monad m => CYT m a -> CYT m a
silent act = censor (const []) act

-- |Warning with a source code position and a `String` indicating
-- the cause of the warning.
warnMessageAt :: Monad m => Span -> String -> CYT m ()
warnMessageAt sp s = warnMessage $ spanMessage sp $ text s

-- |Lift a value into the `CYT m` monad, same as `return`.
ok :: Monad m => a -> CYT m a
ok = return

-- |Lift a pure action into an action based on another monad.
liftCYM :: Monad m => CYM a -> CYT m a
liftCYM = mapWriterT (mapExceptT (return . runIdentity))
