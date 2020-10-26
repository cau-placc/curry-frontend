{-# LANGUAGE ViewPatterns #-}
{- |
    Module      :  $Header$
    Description :  Handling of literate Curry files
    Copyright   :  (c) 2009         Holger Siegel
                       2012  - 2014 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Since version 0.7 of the language report, Curry accepts literate
    source programs. In a literate source, all program lines must begin
    with a greater sign in the first column. All other lines are assumed
    to be documentation. In order to avoid some common errors with
    literate programs, Curry requires at least one program line to be
    present in the file. In addition, every block of program code must be
    preceded by a blank line and followed by a blank line.

    It is also possible to use "\begin{code}" and "\end{code}"
    to mark code segments. Both styles can be used in mixed fashion.
-}

module Curry.Files.Unlit (isLiterate, unlit) where

import Control.Monad         (when, unless, zipWithM)
import Data.Char             (isSpace)
import Data.List             (stripPrefix)

import Curry.Base.Monad      (CYM, failMessageAt)
import Curry.Base.Span       (pos2Span)
import Curry.Base.Position   (Position (..), first)
import Curry.Files.Filenames (lcurryExt, takeExtension)

-- |Check whether a 'FilePath' represents a literate Curry module
isLiterate :: FilePath -> Bool
isLiterate = (== lcurryExt) . takeExtension

-- |Data type representing different kind of lines in a literate source
data Line
  = ProgramStart !Int        -- ^ \begin{code}
  | ProgramEnd   !Int        -- ^ \end{code}
  | Program      !Int String -- ^ program line with a line number and content
  | Comment      !Int String -- ^ comment line
  | Blank        !Int        -- ^ blank line

-- |Process a curry program into error messages (if any) and the
-- corresponding non-literate program.
unlit :: FilePath -> String -> CYM String
unlit fn cy
  | isLiterate fn = do
      let cyl = lines cy
      ls <- progLines fn =<<
            normalize fn (length cyl) False (zipWith classify [1 .. ] cyl)
      when (all null ls) $ failMessageAt (pos2Span $ first fn) "No code in literate script"
      return (unlines ls)
  | otherwise     = return cy

-- |Classification of a single program line
classify :: Int -> String -> Line
classify l s@('>' : _) = Program l s
classify l s@(stripPrefix "\\begin{code}" -> Just cs)
  | all isSpace cs = ProgramStart l
  | otherwise      = Comment l s
classify l s@(stripPrefix "\\end{code}" -> Just cs)
  | all isSpace cs = ProgramEnd l
  | otherwise      = Comment l s
classify l s
  | all isSpace s = Blank l
  | otherwise     = Comment l s

-- |Check that ProgramStart and ProgramEnd match and desugar them.
normalize :: FilePath -> Int -> Bool -> [Line] -> CYM [Line]
normalize _  _ False [] = return []
normalize fn n True  [] = reportMissingEnd fn n
normalize fn n b (ProgramStart l : rest) = do
  when b $ reportSpurious fn l "\\begin{code}"
  norm <- normalize fn n True rest
  return (Blank l : norm)
normalize fn n b (ProgramEnd   l : rest) = do
  unless b $ reportSpurious fn l "\\end{code}"
  norm <- normalize fn n False rest
  return (Blank l : norm)
normalize fn n b (Comment l s : rest) = do
  let cons = if b then Program l s else Comment l s
  norm <- normalize fn n b rest
  return (cons : norm)
normalize fn n b (Program l s : rest) = do
  let cons = if b then Program l s else Program l (drop 1 s)
  norm <- normalize fn n b rest
  return (cons : norm)
normalize fn n b (Blank   l   : rest) = do
  let cons = if b then Program l "" else Blank l
  norm <- normalize fn n b rest
  return (cons : norm)

-- |Check that each program line is not adjacent to a comment line.
progLines :: FilePath -> [Line] -> CYM [String]
progLines fn cs = zipWithM checkAdjacency (Blank 0 : cs) cs where
  checkAdjacency (Program p _) (Comment _ _) = reportBlank fn p "followed"
  checkAdjacency (Comment _ _) (Program p _) = reportBlank fn p "preceded"
  checkAdjacency _             (Program _ s) = return s
  checkAdjacency _             _             = return ""

-- |Compute an appropiate error message
reportBlank :: FilePath -> Int -> String -> CYM a
reportBlank f l cause = failMessageAt (pos2Span $ Position f l 1) msg
  where msg = concat [ "When reading literate source: "
                     , "Program line is " ++ cause ++ " by comment line."
                     ]

reportMissingEnd :: FilePath -> Int -> CYM a
reportMissingEnd f l = failMessageAt (pos2Span $ Position f (l+1) 1) msg
  where msg = concat [ "When reading literate source: "
                     , "Missing '\\end{code}' at the end of file."
                     ]


reportSpurious :: FilePath -> Int -> String -> CYM a
reportSpurious f l cause = failMessageAt (pos2Span $ Position f l 1) msg
  where msg = concat [ "When reading literate source: "
                     , "Spurious '" ++ cause ++ "'."
                     ]
