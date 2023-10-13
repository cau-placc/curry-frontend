{-# LANGUAGE DeterminismSignatures #-}
{-# OPTIONS_FRONTEND -Werror       #-}
module DetSigOverlap where

overlaps :? Det -> Any
overlaps :: Bool -> Bool
overlaps True = False
overlaps _    = True
