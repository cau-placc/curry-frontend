{- |
    Module      : $Header$
    Description : Functions for reading and writing FlatCurry files
    Copyright   : (c) 2014        Björn Peemöller
                      2017        Finn Teegen
    License     : BSD-3-clause

    Maintainer  : bjp@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This module contains functions for reading and writing FlatCurry files.
-}

module Curry.FlatCurry.Files
  ( readTypedFlatCurry, readFlatCurry, readFlatInterface
  , writeFlatCurry, writeBinaryFlatCurry
  ) where

import Data.Binary           (Binary, encode)
import Data.Char             (isSpace)

import Curry.Files.Filenames (typedFlatName, flatName, flatIntName)
import Curry.Files.PathUtils (writeModule, writeBinaryModule, readModule)

import Curry.FlatCurry.Type  (Prog)
import Curry.FlatCurry.Annotated.Type (AProg, TypeExpr)


-- ---------------------------------------------------------------------------
-- Functions for reading and writing FlatCurry terms
-- ---------------------------------------------------------------------------

-- |Reads an typed FlatCurry file (extension ".tfcy") and eventually
-- returns the corresponding FlatCurry program term (type 'AProg').
readTypedFlatCurry :: FilePath -> IO (Maybe (AProg TypeExpr))
readTypedFlatCurry = readFlat . typedFlatName

-- |Reads a FlatCurry file (extension ".fcy") and eventually returns the
-- corresponding FlatCurry program term (type 'Prog').
readFlatCurry :: FilePath -> IO (Maybe Prog)
readFlatCurry = readFlat . flatName

-- |Reads a FlatInterface file (extension @.fint@) and returns the
-- corresponding term (type 'Prog') as a value of type 'Maybe'.
readFlatInterface :: FilePath -> IO (Maybe Prog)
readFlatInterface = readFlat . flatIntName

-- |Reads a Flat file and returns the corresponding term (type 'Prog' or
-- 'AProg') as a value of type 'Maybe'.
-- Due to compatibility with PAKCS it is allowed to have a commentary
-- at the beginning of the file enclosed in {- ... -}.
readFlat :: Read a => FilePath -> IO (Maybe a)
readFlat = fmap (fmap (read . skipComment)) . readModule where
  skipComment s = case dropWhile isSpace s of
      '{' : '-' : s' -> dropComment s'
      s'             -> s'
  dropComment ('-' : '}' : xs) = xs
  dropComment (_ : xs)         = dropComment xs
  dropComment []               = []

-- |Writes a FlatCurry program term into a file.
writeFlatCurry :: Show a => FilePath -> a -> IO ()
writeFlatCurry fn = writeModule fn . show

-- |Writes a FlatCurry program term into a normal and a binary file.
writeBinaryFlatCurry :: Binary a => FilePath -> a -> IO ()
writeBinaryFlatCurry fn = writeBinaryModule fn . encode
