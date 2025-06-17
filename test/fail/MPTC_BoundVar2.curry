{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}


class R a b where

class Q a where

instance R a b => Q [a] where
