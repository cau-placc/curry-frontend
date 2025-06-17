-- Dummy type used to represent a concrete type that is visible to the compiler
-- but not imported as an identifier (IORef).
data ActualIORef a

newIORef :: Int -> IO (ActualIORef Int)
newIORef = failed

-- Curry will interpret this as `Int -> IO (a Int)` due to the default case mode
-- and therefore errors with a 'Type signature too general' error. This is
-- perhaps a bit counter-intuitive to users, see
-- https://git.ps.informatik.uni-kiel.de/curry/curry-frontend/-/issues/155
-- This test therefore ensures that a case mode warning is emitted even though
-- the program fails to compile as a whole.

f :: Int -> IO (IORef Int)
f n = do
  x <- newIORef 42
  return x
