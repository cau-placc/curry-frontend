-- data
data D = C1 Int
       | C2 String
       | C3 Bool
data RD1 = RD1 {}
data RD2 = RD2 { x,y,z :: Int, a :: Bool, r :: RD1 }
data RD3 a = RD3 { f :: a }

-- newtype
newtype RN = RN { x :: Int }

-- record construction
r1 = R1 { x = 12, y = False }
r2 = R2 { }
r3 = R3 { x = 42,  r = r3 }

-- record selection
i = x r3

-- record update
r3' = r3 { x = 24, y = 72 }
r3' = (r r3) { x = 24, y = 72 }

r3' = (r3 { })

-- record pattern
f' R1 { x = 45 } = True
f' R1 { x = 45, y = False } = True
f' R1 { } = True
