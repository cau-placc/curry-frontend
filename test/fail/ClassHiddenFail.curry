module ClassHiddenFail where

import ClassHiddenExport

instance A Bool where
  methodA = True
  methodB = False
