{-# LANGUAGE DeterminismSignatures #-}
module DetSigExport where

class SomeClass a where
  someFunc :: a

  someFuncDefault :: a -> a
  someFuncDefault = id

  someFuncDetSig :: a -> a -> a
  someFuncDetSig :? Det -> Det -> Det

notAClassMethod :: SomeClass a => a
notAClassMethod = someFunc

nondetF1 :: Bool -> Bool
nondetF1 :? Any
nondetF1 = not ? id

nondetF2 :: Bool -> Bool
nondetF2 :? Any -> Any
nondetF2 x = id x ? not x

detF2 :: Bool -> Bool
detF2 :? Det -> Det
detF2 = id
