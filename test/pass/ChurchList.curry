{-# LANGUAGE RankNTypes #-}

newtype ChurchList a =
  ChurchList { runList :: forall r. (a -> r -> r) -> r -> r }

empty :: ChurchList a
empty = ChurchList $ \_ z -> z

fromList :: [a] -> ChurchList a
fromList xs = ChurchList $ \k z -> foldr k z xs

toList :: ChurchList a -> [a]
toList xs = runList xs (:) []

cons :: a -> ChurchList a -> ChurchList a
cons x xs = ChurchList $ \k z -> k x (runList xs k z)

append :: ChurchList a -> ChurchList a -> ChurchList a
append xs ys = ChurchList $ \k z -> runList xs k (runList ys k z)
