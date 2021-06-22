{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCInstanceTermination where

class C a b

instance C a a => C [a] Bool

instance C a b => C [a] Int

class D a

instance C a a => D [a]
