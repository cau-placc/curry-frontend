{-# LANGUAGE RankNTypes #-}

import Prelude hiding (Monad (..))

data Monad m = Monad {
  return :: forall a. a -> m a,
  bind   :: forall a b. m a -> (a -> m b) -> m b
}

listMonad :: Monad []
listMonad = Monad (:[]) (flip concatMap)

maybeMonad :: Monad Maybe
maybeMonad = Monad Just (\m f -> case m of
                                   Nothing -> Nothing
                                   Just x  -> f x)

sequence :: Monad m -> [m a] -> m [a]
sequence m []     = return m []
sequence m (x:xs) = bind m x $ \y -> bind m (sequence m xs)
                             $ \ys -> return m (y:ys)

mapM :: Monad m -> (a -> m b) -> [a] -> m [b]
mapM m f = sequence m . map f

forM :: Monad m -> [a] -> (a -> m b) -> m [b]
forM m = flip (mapM m)

liftM :: Monad m -> (a -> b) -> m a -> m b
liftM m f act = bind m act (return m . f)

liftM2 :: Monad m -> (a -> b -> c) -> m a -> m b -> m c
liftM2 m f act1 act2 = bind m act1 $ \x -> bind m act2
                                   $ \y -> return m (f x y)

foldM :: Monad m -> (a -> b -> m a) -> a -> [b] -> m a
foldM m _ z []     = return m z
foldM m f z (x:xs) = bind m (f z x) (\z' -> foldM m f z' xs)

unlessM :: Monad m -> Bool -> m () -> m ()
unlessM m p act = if p then return m () else act

whenM :: Monad m -> Bool -> m () -> m ()
whenM m p act = if p then act else return m ()
