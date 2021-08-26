{-# LANGUAGE MultiParamTypeClasses, FunctionalPatterns #-}
{-# OPTIONS_FRONTEND -Wno-overlapping #-}

module MPTCListLike where

class ListLike l e where
  emptyL :: l e
  insertL :: e -> l e -> l e
  isEmptyL :: l e -> Bool
  headL :: l e -> e
  tailL :: l e -> l e

instance ListLike [] Bool where
  emptyL = []
  insertL = (:)
  isEmptyL = null
  headL []    = failed
  headL (e:_) = e
  tailL []    = failed
  tailL (_:l) = l

instance ListLike [] Int where
  emptyL = []
  insertL = (:)
  isEmptyL = null
  headL []    = failed
  headL (e:_) = e
  tailL []    = failed
  tailL (_:l) = l

data IntDummy _ = IntDummy Int
  deriving Show

instance ListLike IntDummy Bool where
  emptyL = IntDummy 1
  insertL False (IntDummy n) = IntDummy (n * 2)
  insertL True  (IntDummy n) = IntDummy (n * 2 + 1)
  isEmptyL (IntDummy n) = n == 1
  headL (IntDummy n) | n == 1    = failed
                     | otherwise = mod n 2 == 1
  tailL (IntDummy n) | n == 1    = failed
                     | otherwise = IntDummy (div n 2)

instance ListLike [] [a] where
  emptyL = []
  insertL = (:)
  isEmptyL = null
  headL []    = failed
  headL (e:_) = e
  tailL []    = failed
  tailL (_:l) = l

insertTwoL :: ListLike l e => e -> e -> l e -> l e
insertTwoL e1 e2 = insertL e1 . insertL e2

elemL :: (ListLike l e, Eq e) => e -> l e -> Bool
elemL e l = not (isEmptyL l) && (headL l == e || elemL e (tailL l))

mapLRestricted :: ListLike l e => (e -> e) -> l e -> l e
mapLRestricted = mapLGeneral

mapLGeneral :: (ListLike l1 e1, ListLike l2 e2) => (e1 -> e2) -> l1 e1 -> l2 e2
mapLGeneral f l = if isEmptyL l then emptyL
                                else insertL (f (headL l)) (mapLGeneral f (tailL l))

tailsLDet :: (ListLike l1 e, ListLike l2 (l1 e), Data e, Data (l1 e))
          => l1 e -> l2 (l1 e)
tailsLDet l | isEmptyL l = insertL emptyL         emptyL
tailsLDet (insertL x l)  = insertL (insertL x l) (tailsLDet l)

tailsLNonDet :: (ListLike l e, Data e, Data (l e)) => l e -> l e
tailsLNonDet l             = l
tailsLNonDet (insertL _ l) = tailsLNonDet l

-- Expected result: True
testExp1 :: Bool
testExp1 = elemL False (insertTwoL False True (IntDummy 1))

-- Expected result: [False, True, False]
testExp2 :: [Bool]
testExp2 = mapLRestricted not [True, False, True]

-- Expected result: IntDummy 13
testExp3 :: IntDummy Bool
testExp3 = mapLGeneral id [True, False, True]

-- Expected result: [False, True, False, False, True]
testExp4 :: [Bool]
testExp4 =
  mapLGeneral id (mapLGeneral (> 0) [0 :: Int, 10, -5, -1, 42] :: IntDummy Bool)

-- Expected result: [[1, 2, 3], [2, 3], [3], []]
testExp5 :: [[Int]]
testExp5 = tailsLDet [1, 2, 3]

-- Expected results:
--   [1, 2, 3]
--   [2, 3]
--   [3]
--   []
testExp6 :: [Int]
testExp6 = tailsLNonDet [1, 2, 3]
