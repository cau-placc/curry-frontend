import Prelude hiding ((.))

(.) :: (b -> c) -> (a -> b) -> a -> c
(f . g) x = f (g x)
