{- |
    Module      :  $Header$
    Description :  Abstract syntax for conditional compiling
    Copyright   :  (c) 2017        Kai-Oliver Prott
                       2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  fte@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    TODO
-}
module Curry.CondCompile.Type
  ( Program, Stmt (..), Else (..), Elif (..), Cond (..), Op (..)
  ) where

import Prelude hiding ((<>))

import Curry.Base.Pretty

type Program = [Stmt]

data Stmt = If Cond [Stmt] [Elif] Else
          | IfDef String [Stmt] [Elif] Else
          | IfNDef String [Stmt] [Elif] Else
          | Define String Int
          | Undef String
          | Line String
  deriving Show

newtype Else = Else (Maybe [Stmt])
  deriving Show

newtype Elif = Elif (Cond, [Stmt])
  deriving Show

data Cond = Comp String Op Int
          | Defined String
          | NDefined String
  deriving Show

data Op = Eq
        | Neq
        | Lt
        | Leq
        | Gt
        | Geq
  deriving Show

instance Pretty Stmt where
  pPrint (If     c stmts is e) = prettyIf "#if"     (pPrint c) stmts is e
  pPrint (IfDef  v stmts is e) = prettyIf "#ifdef"  (text v)   stmts is e
  pPrint (IfNDef v stmts is e) = prettyIf "#ifndef" (text v)   stmts is e
  pPrint (Define v i         ) = text "#define" <+> text v <+> int i
  pPrint (Undef  v           ) = text "#undef"  <+> text v
  pPrint (Line   s           ) = text s

  pPrintList = foldr (($+$) . pPrint) empty

instance Pretty Elif where
  pPrint (Elif (c, stmts)) = text "#elif" <+> pPrint c $+$ pPrint stmts

  pPrintList = foldr (($+$) . pPrint) empty

instance Pretty Else where
  pPrint (Else (Just stmts)) = text "#else" $+$ pPrint stmts
  pPrint (Else Nothing)      = empty

prettyIf :: String -> Doc -> [Stmt] -> [Elif] -> Else -> Doc
prettyIf k doc stmts is e = foldr ($+$) empty
  [text k <+> doc, pPrint stmts, pPrint is, pPrint e, text "#endif"]

instance Pretty Cond where
  pPrint (Comp v op i) = text v <+> pPrint op <+> int i
  pPrint (Defined  v ) = text "defined("  <> text v <> char ')'
  pPrint (NDefined v ) = text "!defined(" <> text v <> char ')'

instance Pretty Op where
  pPrint Eq  = text "=="
  pPrint Neq = text "/="
  pPrint Lt  = text "<"
  pPrint Leq = text "<="
  pPrint Gt  = text ">"
  pPrint Geq = text ">="
