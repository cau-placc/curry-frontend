{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCSuperClasses where

class C a where
  methodC :: a

class (C b, C c) => D a b c where
  methodD :: a b c

class D a b b => E a b where
  methodE :: a b Bool

class F where
  methodF :: Bool

class (D a c c, D b c c, F) => G a b c where
  methodG :: a c (b c c)

instance C Bool where
  methodC = True

instance D (,) Bool Bool where
  methodD = (methodC, methodC)

instance D Either Bool Bool where
  methodD = Left False

instance E (,) Bool where
  methodE = methodD

instance F where
  methodF = False

instance G (,) Either Bool where
  methodG = if methodF then (True, methodD) else (False, Right True)

f1 :: D a b c => (a b c, b, c)
f1 = (methodD, methodC, methodC)

f2 :: E a b => a b b
f2 = methodD

f3 :: G a a b => (a b (a b b), Bool)
f3 = (methodG, methodF)

-- Expected result: (False, Right True)
testExp1 :: (Bool, Either Bool Bool)
testExp1 = methodG

-- Expected result: (True, True)
testExp2 :: (Bool, Bool)
testExp2 = let methodD' = methodD in (fst methodE, fst methodD' && snd methodD')
