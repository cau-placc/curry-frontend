{-# LANGUAGE DeterminismSignatures #-}

double :? Any
double :? Det -> Det
double :: Int -> Int
double x = x + x
