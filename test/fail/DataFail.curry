data Test1   = Test1 (Test2 Int)

data Test2 a = Test2 Test1 a (a -> a)

test1Fail :: Test1
test1Fail = a where a free

test2Fail :: Data a => Test2 a
test2Fail = unknown

test3Fail :: (Test1, Test2 a)
test3Fail = (aValue, aValue)
