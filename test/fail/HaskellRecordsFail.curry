-- newtype
-- should NOT be parsed
newtype RN = RN { x,y :: Int }
newtype RN = RN { x :: Int, y :: Bool }
newtype RN = RN { }
