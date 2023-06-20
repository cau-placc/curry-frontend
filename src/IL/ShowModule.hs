{- |
    Module      :  $Header$
    Description :  Custom Show implementation for IL
    Copyright   :  (c) 2015        Björn Peemöller
                       2016 - 2017 Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements a generic show function comparable to the one
   obtained by @deriving Show@. However, the internal representation of
   identifiers is hidden to avoid syntactic clutter.
-}

module IL.ShowModule (showModule) where

import Curry.Base.Ident
import Curry.Base.Position

import IL.Type

-- |Show a IL module like by an devired 'Show' instance
showModule :: Module -> String
showModule m = showsModule m "\n"

showsModule :: Module -> ShowS
showsModule (Module mident imps decls)
  = showsString "Module "
  . showsModuleIdent mident . newline
  . showsList (\i -> showsModuleIdent i . newline) imps
  . showsList (\d -> showsDecl d . newline) decls

showsDecl :: Decl -> ShowS
showsDecl (DataDecl qident arity constrdecls)
  = showsString "(DataDecl "
  . showsQualIdent qident . space
  . shows arity . space
  . showsList showsConstrDecl constrdecls
  . showsString ")"
showsDecl (NewtypeDecl qident arity newconstrdecl)
  = showsString "(NewtypeDecl "
  . showsQualIdent qident . space
  . shows arity . space
  . showsNewConstrDecl newconstrdecl
  . showsString ")"
showsDecl (ExternalDataDecl qident arity)
  = showsString "(ExternalDataDecl "
  . showsQualIdent qident . space
  . shows arity
  . showsString ")"
showsDecl (FunctionDecl qident idents typ expr)
  = showsString "(FunctionDecl "
  . showsQualIdent qident . space
  . showsList (showsIdent . snd) idents . space
  . showsType typ . space
  . showsExpression expr
  . showsString ")"
showsDecl (ExternalDecl qident arity typ)
  = showsString "(ExternalDecl "
  . showsQualIdent qident . space
  . shows arity
  . showsType typ
  . showsString ")"

showsConstrDecl :: ConstrDecl -> ShowS
showsConstrDecl (ConstrDecl qident tys)
  = showsString "(ConstrDecl "
  . showsQualIdent qident . space
  . showsList showsType tys
  . showsString ")"

showsNewConstrDecl :: NewConstrDecl -> ShowS
showsNewConstrDecl (NewConstrDecl qident ty)
  = showsString "(NewConstrDecl "
  . showsQualIdent qident . space
  . showsType ty
  . showsString ")"

showsType :: Type -> ShowS
showsType (TypeConstructor qident types)
  = showsString "(TypeConstructor "
  . showsQualIdent qident . space
  . showsList showsType types
  . showsString ")"
showsType (TypeVariable int)
  = showsString "(TypeVariable "
  . shows int
  . showsString ")"
showsType (TypeArrow type1 type2)
  = showsString "(TypeArrow "
  . showsType type1 . space
  . showsType type2
  . showsString ")"
showsType (TypeForall ints typ)
  = showsString "(TypeForall "
  . showsList shows ints . space
  . showsType typ
  . showsString ")"

showsLiteral :: Literal -> ShowS
showsLiteral (Char c)
  = showsString "(Char "
  . shows c
  . showsString ")"
showsLiteral (Int n)
  = showsString "(Int "
  . shows n
  . showsString ")"
showsLiteral (Float x)
  = showsString "(Float "
  . shows x
  . showsString ")"
showsLiteral (String x)
  = showsString "(String "
  . shows x
  . showsString ")"

showsConstrTerm :: ConstrTerm -> ShowS
showsConstrTerm (LiteralPattern ty lit)
  = showsString "(LiteralPattern "
  . showsType ty
  . showsLiteral lit
  . showsString ")"
showsConstrTerm (ConstructorPattern ty qident idents)
  = showsString "(ConstructorPattern "
  . showsType ty
  . showsQualIdent qident . space
  . showsList (showsIdent . snd) idents
  . showsString ")"
showsConstrTerm (VariablePattern ty ident)
  = showsString "(VariablePattern "
  . showsType ty
  . showsIdent ident
  . showsString ")"

showsExpression :: Expression -> ShowS
showsExpression (Literal ty lit)
  = showsString "(Literal "
  . showsType ty
  . showsLiteral lit
  . showsString ")"
showsExpression (Variable ty ident)
  = showsString "(Variable "
  . showsType ty
  . showsIdent ident
  . showsString ")"
showsExpression (Function ty qident int)
  = showsString "(Function "
  . showsType ty
  . showsQualIdent qident . space
  . shows int
  . showsString ")"
showsExpression (Constructor ty qident int)
  = showsString "(Constructor "
  . showsType ty
  . showsQualIdent qident . space
  . shows int
  . showsString ")"
showsExpression (Apply exp1 exp2)
  = showsString "(Apply "
  . showsExpression exp1 . space
  . showsExpression exp2
  . showsString ")"
showsExpression (Case eval expr alts)
  = showsString "(Case "
  . showsEval eval . space
  . showsExpression expr . space
  . showsList showsAlt alts
  . showsString ")"
showsExpression (Or exp1 exp2)
  = showsString "(Or "
  . showsExpression exp1 . space
  . showsExpression exp2
  . showsString ")"
showsExpression (Exist ident ty expr)
  = showsString "(Exist "
  . showsIdent ident . space
  . showsType ty . space
  . showsExpression expr
  . showsString ")"
showsExpression (Let bind expr)
  = showsString "(Let "
  . showsBinding bind . space
  . showsExpression expr
  . showsString ")"
showsExpression (Letrec binds expr)
  = showsString "(Letrec "
  . showsList showsBinding binds . space
  . showsExpression expr
  . showsString ")"
showsExpression (Typed expr typ)
  = showsString "(Typed "
  . showsExpression expr . space
  . showsType typ
  . showsString ")"

showsEval :: Eval -> ShowS
showsEval Rigid = showsString "Rigid"
showsEval Flex  = showsString "Flex"

showsAlt :: Alt -> ShowS
showsAlt (Alt constr expr)
  = showsString "(Alt "
  . showsConstrTerm constr . space
  . showsExpression expr
  . showsString ")"

showsBinding :: Binding -> ShowS
showsBinding (Binding ident expr)
  = showsString "(Binding "
  . showsIdent ident . space
  . showsExpression expr
  . showsString ")"

showsPosition :: Position -> ShowS
showsPosition Position { line = l, column = c } = showsPair shows shows (l, c)
showsPosition _ = showsString "(0,0)"

showsString :: String -> ShowS
showsString = (++)

space :: ShowS
space = showsString " "

newline :: ShowS
newline = showsString "\n"

showsMaybe :: (a -> ShowS) -> Maybe a -> ShowS
showsMaybe shs = maybe (showsString "Nothing")
                       (\x -> showsString "(Just " . shs x . showsString ")")

showsList :: (a -> ShowS) -> [a] -> ShowS
showsList _   [] = showsString "[]"
showsList shs (x:xs)
  = showsString "["
  . foldl (\sys y -> sys . showsString "," . shs y) (shs x) xs
  . showsString "]"

showsPair :: (a -> ShowS) -> (b -> ShowS) -> (a,b) -> ShowS
showsPair sa sb (a,b)
  = showsString "(" . sa a . showsString "," . sb b . showsString ")"

showsIdent :: Ident -> ShowS
showsIdent (Ident spi x n)
  = showsString "(Ident " . showsPosition (getPosition spi) . space
  . shows x . space . shows n . showsString ")"

showsQualIdent :: QualIdent -> ShowS
showsQualIdent (QualIdent _ mident ident)
  = showsString "(QualIdent "
  . showsMaybe showsModuleIdent mident
  . space
  . showsIdent ident
  . showsString ")"

showsModuleIdent :: ModuleIdent -> ShowS
showsModuleIdent (ModuleIdent spi ss)
  = showsString "(ModuleIdent "
  . showsPosition (getPosition spi) . space
  . showsList (showsQuotes showsString) ss
  . showsString ")"

showsQuotes :: (a -> ShowS) -> a -> ShowS
showsQuotes sa a
  = showsString "\"" . sa a . showsString "\""
