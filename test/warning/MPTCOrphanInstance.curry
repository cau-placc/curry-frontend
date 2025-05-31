{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_FRONTEND -Worphan-instances #-}

module MPTCOrphanInstance where

import MPTCIncompleteInstance

instance C Foo Bool where
  methodC1 Foo = True
  methodC2 _ _ = False
  methodC3 _   = Foo

instance E where
  methodE = False
