{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCMissingSuperClassInstance where

class C a b

class C b a => D a b

instance C Bool Int

instance D Bool Int

instance C (a, b) (a, c)

instance C (a, b) (c, b)

instance D (a, b) (b, a)

instance D (a, b) (a, b)

class E

class (D a a, E) => F a

instance F Bool
