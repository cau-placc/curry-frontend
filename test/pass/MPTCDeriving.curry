{-# LANGUAGE MultiParamTypeClasses #-}

module MPTCDeriving where

class C a b where
  showAB :: a -> b -> String

data Foo a b = Foo a b

instance C a b => Show (Foo a b) where
  show (Foo x y) = "(Foo " ++ showAB x y ++ ")"

data Bar a b = Bar (Foo a b)
  deriving Show

showBar :: C a b => Bar a b -> String
showBar = show

instance C Bool Char where
  showAB b c = show b ++ ' ' : show c

-- Expected result: "Bar (Foo False 'f')"
testExp :: String
testExp = show (Bar (Foo False 'f'))
