{-# LANGUAGE DeterminismSignatures #-}
module DetSigFail where

import DetSigExport

instance SomeClass Bool where
  someFunc = True

  someFuncDetSig = someFuncDetSig ? someFuncDetSig

detF1 :: Bool -> Bool
detF1 :? Det
detF1 = not

use1 :? Det
use1 :: Bool
use1 = nondetF1 True

use2 :? Det
use2 :: Bool
use2 = nondetF2 True

use3 :? Det
use3 :: Bool
use3 = detF1 (True ? False)

use4 :? Det
use4 :: Bool
use4 = detF2 (True ? False)

use5 :? Det
use5 :: Bool
use5 = notAClassMethod
