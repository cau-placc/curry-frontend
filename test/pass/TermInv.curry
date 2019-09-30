{-# LANGUAGE RankNTypes #-}

data Term a = Var a
            | App (Term a) (Term a)
            | Lam (Term (Incr a))

data Incr a = Zero | Succ a

mapI :: (a -> b) -> Incr a -> Incr b
mapI _ Zero     = Zero
mapI f (Succ x) = Succ (f x)

type MapT = forall a b. (a -> b) -> Term a -> Term b

fixMT :: (MapT -> MapT) -> MapT
fixMT f = f (fixMT f)

mapT :: MapT
mapT = fixMT (\mt -> \f t -> case t of
  Var x     -> Var (f x)
  App t1 t2 -> App (mt f t1) (mt f t2)
  Lam t'    -> Lam (mt (mapI f) t'))

foldT :: (forall a. a -> n a)
      -> (forall a. n a -> n a -> n a)
      -> (forall a. n (Incr a) -> n a)
      -> Term b -> n b
foldT v _ _ (Var x)     = v x
foldT v a l (App t1 t2) = a (foldT v a l t1) (foldT v a l t2)
foldT v a l (Lam t)     = l (foldT v a l t)
