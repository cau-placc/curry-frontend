{- |
    Module      :  $Header$
    Description :  Library to support meta-programming in Curry
    Copyright   :  (c) Michael Hanus  , 2004
                       Martin Engelke , 2005
                       Björn Peemöller, 2014
                       Finn Teegen    , 2016
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This library contains I/O actions to read Curry programs
    and transform them into this abstract representation as well as
    write them to a file.
-}
module Curry.AbstractCurry.Files
  ( readCurry, writeCurry, showCurry
  ) where

import qualified Control.Exception        as C (catch)
import           Data.List                     (intercalate)

import           Curry.Files.PathUtils         ( writeModule, readModule
                                               , addVersion, checkVersion)

import           Curry.AbstractCurry.Type

-- ---------------------------------------------------------------------------
-- Reading and writing AbstractCurry terms
-- ---------------------------------------------------------------------------

-- |Read an AbstractCurry file and return the corresponding AbstractCurry
--  program term of type 'CurryProg'
readCurry :: FilePath -> IO (Maybe CurryProg)
readCurry fn = do
  mbSrc <- readModule fn
  return $ case mbSrc of
    Nothing  -> Nothing
    Just src -> case checkVersion version src of
      Left  _  -> Nothing
      Right ac -> Just (read ac)

-- |Write an AbstractCurry program term into a file.
writeCurry :: FilePath -> CurryProg -> IO ()
writeCurry fn p = C.catch (writeModule fn $ addVersion version $ showCurry p)
                  ioError

-- |Show an AbstractCurry program in a nicer way
showCurry :: CurryProg -> String
showCurry (CurryProg mname imps dflt clss insts types funcs ops)
  =  "CurryProg " ++ show mname ++ "\n"
  ++ show imps ++ "\n"
  ++ showsPrec 11 dflt "\n"
  ++ wrapList clss
  ++ wrapList insts
  ++ wrapList types
  ++ wrapList funcs
  ++ wrapList ops
  where wrapList xs = " [" ++ intercalate ",\n  " (map show xs) ++ "]\n"
