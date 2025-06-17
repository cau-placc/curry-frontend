-- The default case mode `curry` should behave like `haskell`, but warn instead of failing.
module CaseModeC where

func :: (a -> B) -> [a] -> [B]
func mf Xs = map mf Xs

data c = E | f
