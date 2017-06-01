{-# OPTIONS_FRONTEND --case-mode=prolog #-}
module CaseModeP where

func :: (a -> B) -> [a] -> [B]
func mf Xs = map mf Xs

data c = E | f
