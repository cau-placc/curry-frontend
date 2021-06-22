{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCSuperClassCycle where

class E b => C a b c

class C b b a => D a b

class D a a => E a

class G => F

class F => G
