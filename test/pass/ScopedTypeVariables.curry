{-# LANGUAGE ExplicitForAll      #-}
{-# LANGUAGE ScopedTypeVariables #-}

fun1 :: forall a. [a] -> [a]
fun1 xs = ys ++ ys
  where
    ys :: [a]
    ys = reverse xs

fun2 :: forall a. [a] -> [a]
fun2 (x:xs) = xs ++ [x :: a]

fun3 :: forall a. [a] -> [a]
fun3 = \(x:xs) -> xs ++ [x :: a]

fun4 :: a -> b -> (a, b)
fun4 x y = (idFun x, idFun y)
  where
    idFun :: a -> a
    idFun = id

fun5 = (\x y -> let g :: a -> a
                    g = id
                 in (g x, y)) :: forall a b. a -> b -> (a, b)

class A a where
  funA :: [a] -> a
  funA xs = let ys :: [a]
                ys = reverse xs
             in head ys

instance A b => A [b] where
  funA xs = reverse (head (xs :: [[b]]))

class B a where
  funB :: a -> a

instance B [b] where
  funB xs = let ys :: [b]
                ys = reverse xs
             in ys ++ ys
