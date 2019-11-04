{-# LANGUAGE FunctionalPatterns #-}
{-# LANGUAGE RankNTypes         #-}

funH :: (forall c. Int -> c) -> a -> b -> Int
funH g (funF g x) (funF g y) = x + y

funF :: (a -> b) -> a -> b
funF g a = g a

funHTest :: Int
funHTest = funH (\x -> error "fail") 4 4
