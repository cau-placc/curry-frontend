data Func a = Func (forall b. a -> b -> a)

fun :: (forall a. a -> a) -> (Char, Bool)
fun f = (f 'c', f True)

idFun :: (forall a. Eq a => a) -> (forall a. Ord a => a)
idFun x = x

applyFun :: forall a b. (a -> b) -> a -> b
applyFun f x = f x
