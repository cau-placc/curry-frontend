{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

class Collects e ce | ce -> e where
  empty :: ce
  insert :: e -> ce -> ce
  member :: e -> ce -> Bool

f x y = insert x . insert y

-- g :: (Collects Bool c, Collects Char c) => c -> c
g = f True 'a'

h = insert True . insert 'a'
