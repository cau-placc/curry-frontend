{-# OPTIONS_FRONTEND --case-mode=haskell #-}
module CaseModeH where

func :: (a -> B) -> [a] -> [B]
func mf Xs = map mf Xs

data c = E | f
