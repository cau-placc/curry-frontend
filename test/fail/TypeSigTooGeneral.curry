f :: Eq a => a -> Bool
f x = g x
  where
    g y = x == y
    h :: a -> Bool
    h x = g x

f' :: [a] -> [a]
f' xs = g' (reverse xs)
  where
    g' :: [b] -> [b]
    g' ys = xs ++ ys

n :: Show a => f a
n = 23
