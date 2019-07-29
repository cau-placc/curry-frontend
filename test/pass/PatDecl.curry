module PatDecl where

f ys = x:xs
  where (x:xs) = ys

allDifferent = \xss -> let xs = concat xss
                           nub ys = case ys of
                             []   -> []
                             y:ys -> y : nub (filter (/= y) ys)
                        in if nub xs == xs then Just xs else Nothing

allDifferentBool :: [[Bool]] -> Maybe [Bool]
allDifferentBool = allDifferent
