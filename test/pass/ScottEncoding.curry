{-# LANGUAGE RankNTypes #-}

newtype PairS a b = PairS { runPairS :: forall r. (a -> b -> r) -> r }

pairS :: a -> b -> PairS a b
pairS x y = PairS (\p -> p x y)

fstS :: PairS a b -> a
fstS (PairS p) = p (\x _ -> x)

fstS' :: PairS a b -> a
fstS' (PairS p) = p const

sndS :: PairS a b -> b
sndS (PairS p) = p (\_ y -> y)

sndS' :: PairS a b -> b
sndS' (PairS p) = p (flip const)

swapS :: PairS a b -> PairS b a
swapS p = pairS (sndS p) (fstS p)

data PeanoS = PeanoS { runPeanoS :: forall r. (PeanoS -> r) -> r -> r }

zeroS :: PeanoS
zeroS = PeanoS (\_ z -> z)

succS :: PeanoS -> PeanoS
succS n = PeanoS (\s _ -> s n)

runPeanoS' :: (PeanoS -> r) -> r -> PeanoS -> r
runPeanoS' s z (PeanoS f) = f s z

isZeroS :: PeanoS -> Bool
isZeroS = runPeanoS' (const False) True

addS :: PeanoS -> PeanoS -> PeanoS
addS n m = runPeanoS' (\s -> succS (addS s m)) m n

data ListS a = ListS { runListS :: forall r. (a -> ListS a -> r) -> r -> r }

nilS :: ListS a
nilS = ListS (flip const)

consS :: a -> ListS a -> ListS a
consS x xs = ListS (\k _ -> k x xs)

runListS' :: (a -> ListS a -> r) -> r -> ListS a -> r
runListS' k z (ListS f) = f k z

isNullS :: ListS a -> Bool
isNullS = runListS' (\_ _ -> False) True

mapS :: (a -> b) -> ListS a -> ListS b
mapS f = runListS' (\x xs -> consS (f x) (mapS f xs)) nilS

instance Functor ListS where
  fmap = mapS
