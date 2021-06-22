{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCMissingSuperClassInstance where

class C a b

class C b a => D a b

instance C Bool Int

instance D Bool Int

class E

class (D a a, E) => F a

instance F Bool
