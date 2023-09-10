{- |
    Module      :  $Header$
    Description :  Conditional compiling transformation
    Copyright   :  (c) 2017        Finn Teegen
                       2017 - 2023 Kai-Oliver Prott
    License     :  BSD-3-clause

    Maintainer  :  kpr@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines the transformation of a program
    with respect to its conditional compiling directives.

    The result of the transformation is a program where
    all directives are removed and the corresponding lines
    are either included or excluded, depending on the
    definitions of the conditional compiling directives.

    Any removed lines are replaced by empty lines.
-}
module Curry.CondCompile.Transform (condTransform) where

import           Control.Monad.State
import           Control.Monad.Extra        (concatMapM)
import qualified Data.Map            as Map
import           Data.Maybe                 (fromMaybe)
import           Text.Parsec                             hiding (State)
import           Text.Parsec.Error          ()

import Curry.Base.Message
import Curry.Base.Position
import Curry.Base.Pretty

import Curry.CondCompile.Parser
import Curry.CondCompile.Type

type CCState = Map.Map String Int

type CCM = State CCState

condTransform :: CCState -> FilePath -> String -> Either Message String
condTransform s fn p = either (Left . convertError)
                              (Right . transformWith s)
                              (parse program fn p)

transformWith :: CCState -> Program -> String
transformWith s p = show $ pPrint $ evalState (transform p) s

convertError :: ParseError -> Message
convertError err = posMessage pos $
  foldr (($+$) . text) empty (tail $ lines $ show err)
  where pos = Position (sourceName src) (sourceLine src) (sourceColumn src)
        src = errorPos err

class CCTransform a where
  transform :: a -> CCM [Stmt]

instance CCTransform Stmt where
  transform (Line              s) = return [Line s]
  transform (If     c stmts is e) = do
    s <- get
    if checkCond c s
      then do stmts' <- transform stmts
              return (blank : stmts' ++ fill is ++ fill e ++ [blank])
      else case is of
             []                        -> do
               stmts' <- transform e
               return (blank : fill stmts ++ stmts' ++ [blank])
             (Elif (c', stmts') : is') -> do
               stmts'' <- transform (If c' stmts' is' e)
               return (blank : fill stmts ++ stmts'')
  transform (IfDef  v stmts is e) = transform (If (Defined  v) stmts is e)
  transform (IfNDef v stmts is e) = transform (If (NDefined v) stmts is e)
  transform (Define          v i) = modify (Map.insert v i) >> return [blank]
  transform (Undef           v  ) = modify (Map.delete v) >> return [blank]

instance CCTransform a => CCTransform [a] where
  transform = concatMapM transform

instance CCTransform Else where
  transform (Else (Just p)) = (blank :) <$> transform p
  transform (Else Nothing ) = return []

checkCond :: Cond -> CCState -> Bool
checkCond (Comp v op i) = flip (compareOp op) i . fromMaybe 0 . Map.lookup v
checkCond (Defined   v) = Map.member v
checkCond (NDefined  v) = Map.notMember v

compareOp :: Ord a => Op -> a -> a -> Bool
compareOp Eq  = (==)
compareOp Neq = (/=)
compareOp Lt  = (<)
compareOp Leq = (<=)
compareOp Gt  = (>)
compareOp Geq = (>=)

class FillLength a where
  fillLength :: a -> Int

instance FillLength Stmt where
  fillLength (Line   _           ) = 1
  fillLength (Define _ _         ) = 1
  fillLength (Undef  _           ) = 1
  fillLength (If     _ stmts is e) =
    2 + fillLength stmts + fillLength e + fillLength is
  fillLength (IfDef  v stmts is e) = fillLength (If (Defined  v) stmts is e)
  fillLength (IfNDef v stmts is e) = fillLength (If (NDefined v) stmts is e)

instance FillLength a => FillLength [a] where
  fillLength = foldr ((+) . fillLength) 0

instance FillLength Else where
  fillLength (Else (Just stmts)) = 1 + fillLength stmts
  fillLength (Else Nothing     ) = 0

instance FillLength Elif where
  fillLength (Elif (_, stmts)) = 1 + fillLength stmts

fill :: FillLength a => a -> [Stmt]
fill p = replicate (fillLength p) blank

blank :: Stmt
blank = Line ""
