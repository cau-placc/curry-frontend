data P = P { x :: Int, y :: Int, z :: Int, w :: Int }

p :: P
p = P { x = 3, y = 4, z = 5 }

newtype N = N { unN :: Int }

n :: N
n = N {}
