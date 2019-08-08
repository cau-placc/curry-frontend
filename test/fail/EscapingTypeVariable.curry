{-# LANGUAGE RankNTypes #-}

data Bag _ a = Bag a
data Elem _ a = Elem a

instance Monad (Bag s) where
  (>>=) = bindBag
  return = returnBag

bindBag :: Bag s a -> (a -> Bag s b) -> Bag s b
bindBag b f = case b of
                Bag x -> f x

returnBag :: a -> forall s. Bag s a
returnBag = Bag

runBag :: forall a. (forall s. Bag s a) -> a
runBag b = case b of
             Bag x -> x

newElem :: a -> (forall s. Bag s (Elem s a))
newElem = Bag . Elem

readElem :: forall s. forall a. (Elem s a -> Bag s a)
readElem e = case e of
               Elem x -> Bag x

getElemFromBag = runBag (do e <- newElem "Hello, world!"
                            return e)

getElemFromBag' = runBag (newElem "Hello, world!")
