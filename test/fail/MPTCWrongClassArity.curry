{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCWrongClassArity where

class C a

instance C

f1 :: C a b => a -> b
f1 = failed

class D a b

f2 :: D a => a
f2 = failed

instance D Bool Bool Bool

class E

instance E Bool
