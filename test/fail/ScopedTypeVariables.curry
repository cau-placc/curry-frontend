{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

fun1 :: forall a b. a -> b -> (a, b)
fun1 a b = (idFun a, b)
  where
    idFun :: b -> b
    idFun = id

fun2 :: forall a. forall b. a -> [b] -> [b]
fun2 _ (x:xs) = xs ++ [x :: b]

fun3 :: forall a. a -> forall b. [b] -> [b]
fun3 _ (x:xs) = xs ++ [x :: b]

type A = forall b. [b] -> [b]

fun4 :: A
fun4 (x:xs) = xs ++ [x :: b]

fun5 = (\x y -> let g :: a -> a
                    g = id
                 in (g x, g y)) :: forall a b. a -> b -> (a, b)
