module Main (main) where

import Curry.Base.Monad
import Curry.Files.PathUtils

import Curry.Syntax

import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> error $ "Missing argument"
    [file] -> do msrc <-readModule file
                 case msrc of
                   Nothing  -> error $ "Missing file " ++ file
                   Just src -> do let res = runCYM $ do ul <- unlit file src
                                                        parseModule file ul
                                  case res of Left f  -> print f
                                              Right m -> print $ m
