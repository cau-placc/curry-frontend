{-# LANGUAGE RankNTypes #-}

newtype ChurchList a =
  ChurchList { runList :: forall r. (a -> r -> r) -> r -> r }

empty :: ChurchList a
empty = ChurchList (\_ z -> z)

fromList :: [a] -> ChurchList a
fromList xs = ChurchList (\k z -> foldr k z xs)

toList :: ChurchList a -> [a]
toList xs = runList xs (:) []

cons :: a -> ChurchList a -> ChurchList a
cons x xs = ChurchList (\k z -> k x (runList xs k z))

append :: ChurchList a -> ChurchList a -> ChurchList a
append xs ys = ChurchList (\k z -> runList xs k (runList ys k z))

instance Functor ChurchList where
  fmap f xs = ChurchList (\k z -> runList xs (\x xs' -> k (f x) xs') z)

newtype ChurchMaybe a =
  ChurchMaybe { runMaybe :: forall r. r -> (a -> r) -> r }

nothing :: ChurchMaybe a
nothing = ChurchMaybe const

just :: a -> ChurchMaybe a
just x = ChurchMaybe (\_ j -> j x)

isNothing :: ChurchMaybe a -> Bool
isNothing (ChurchMaybe m) = m True (const False)

isJust :: ChurchMaybe a -> Bool
isJust (ChurchMaybe m) = m False (const True)

fromJust :: ChurchMaybe a -> a
fromJust (ChurchMaybe m) = m (error "fail") id

instance Eq a => Eq (ChurchMaybe a) where
  ChurchMaybe m == ChurchMaybe n = m (n True (const False)) (n False . (==))

instance Ord a => Ord (ChurchMaybe a) where
  compare (ChurchMaybe m) (ChurchMaybe n) = m (n EQ (const LT)) (n GT . compare)

instance Show a => Show (ChurchMaybe a) where
  show (ChurchMaybe m) = m "Nothing" (("Just " ++) . show)

instance Functor ChurchMaybe where
  fmap f (ChurchMaybe m) = ChurchMaybe (\n j -> m n (j . f))

instance Monad ChurchMaybe where
  return x = ChurchMaybe (\_ j -> j x)
  ChurchMaybe m >>= f = m nothing f