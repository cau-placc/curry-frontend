{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCInstanceTermination where

class C a b

instance C b b => C [b] Bool

class D a

instance C a a => D [a]
