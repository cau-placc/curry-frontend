--- Polymorphically typed free variables
--- Redmine - curry-frontend - bug #480

test :: Data a => a
test = x
  where
    x :: b
    x = unknown

test0 :: Data a => a
test0 = x
  where
    x free

test1 :: Data a => a
test1 = x
  where
    x :: a
    x free

test2 :: a -> b
test2 = let x = unknown :: a -> b in x

test3 :: a -> b
test3 = let x free in x :: a -> b

test4 :: (Bool, ())
test4 = (x, x)
  where x free

test5 :: (Bool, ())
test5 = (x, x)
  where
    x :: a
    x = unknown

test6 :: a
test6 = let x = x :: a in x
