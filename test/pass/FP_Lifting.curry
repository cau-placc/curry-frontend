{-# LANGUAGE FunctionalPatterns #-}

f x = g x &> x
 where
  g (h y) = success
-- causes an error since h is not global
--h y = x
h y = error "undefined"

main = f z
 where z free
{-

f2 x = g2 x x &> x

g2 x1 z = h2 x2 y =:<= z &> x1 =:= x2 &> success
  where x2, y free

h2 x y = x

main2 = f2 z
 where z free

f3 x = g3 x x &> x

g3 x (h3 x y) = success

h3 x y = x

main3 = f3 z
 where z free

patid x (id x) = x


f5 (id x) (id x) = x
-}
