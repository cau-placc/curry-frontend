{- |
    Module      : $Header$
    Description : Utility functions for working with TypedFlatCurry.
    Copyright   : (c) 2016 - 2017 Finn Teegen
                      2018        Kai-Oliver Prott
    License     : BSD-3-clause

    Maintainer  : fte@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This library provides selector functions, test and update operations
    as well as some useful auxiliary functions for TypedFlatCurry data terms.
    Most of the provided functions are based on general transformation
    functions that replace constructors with user-defined
    functions. For recursive datatypes the transformations are defined
    inductively over the term structure. This is quite usual for
    transformations on TypedFlatCurry terms,
    so the provided functions can be used to implement specific transformations
    without having to explicitly state the recursion. Essentially, the tedious
    part of such transformations - descend in fairly complex term structures -
    is abstracted away, which hopefully makes the code more clear and brief.
-}

module Curry.FlatCurry.Typed.Goodies
  ( module Curry.FlatCurry.Typed.Goodies
  , module Curry.FlatCurry.Goodies
  ) where

import Control.Arrow (first, second)

import Curry.FlatCurry.Goodies ( Update
                               , trType, typeName, typeVisibility, typeParams
                               , typeConsDecls, typeSyn, isTypeSyn
                               , isDataTypeDecl, isExternalType, isPublicType
                               , updType, updTypeName, updTypeVisibility
                               , updTypeParams, updTypeConsDecls, updTypeSynonym
                               , updQNamesInType
                               , trCons, consName, consArity, consVisibility
                               , isPublicCons, consArgs, updCons, updConsName
                               , updConsArity, updConsVisibility, updConsArgs
                               , updQNamesInConsDecl
                               , trNewCons, newConsName, newConsVisibility
                               , isPublicNewCons, newConsArg
                               , updNewCons, updNewConsName
                               , updNewConsVisibility, updNewConsArg
                               , updQNamesInNewConsDecl
                               , tVarIndex, domain, range, tConsName, tConsArgs
                               , trTypeExpr, isTVar, isTCons, isFuncType
                               , updTVars, updTCons, updFuncTypes, argTypes
                               , typeArity, resultType, allVarsInTypeExpr
                               , allTypeCons, rnmAllVarsInTypeExpr
                               , updQNamesInTypeExpr
                               , trOp, opName, opFixity, opPrecedence, updOp
                               , updOpName, updOpFixity, updOpPrecedence
                               , trCombType, isCombTypeFuncCall
                               , isCombTypeFuncPartCall, isCombTypeConsCall
                               , isCombTypeConsPartCall
                               , isPublic
                               )

import Curry.FlatCurry.Typed.Type

-- TProg ----------------------------------------------------------------------

-- |transform program
trTProg :: (String -> [String] -> [TypeDecl] -> [TFuncDecl] -> [OpDecl] -> b)
        -> TProg -> b
trTProg prog (TProg name imps types funcs ops) = prog name imps types funcs ops

-- Selectors

-- |get name from program
tProgName :: TProg -> String
tProgName = trTProg (\name _ _ _ _ -> name)

-- |get imports from program
tProgImports :: TProg -> [String]
tProgImports = trTProg (\_ imps _ _ _ -> imps)

-- |get type declarations from program
tProgTypes :: TProg -> [TypeDecl]
tProgTypes = trTProg (\_ _ types _ _ -> types)

-- |get functions from program
tProgTFuncs :: TProg -> [TFuncDecl]
tProgTFuncs = trTProg (\_ _ _ funcs _ -> funcs)

-- |get infix operators from program
tProgOps :: TProg -> [OpDecl]
tProgOps = trTProg (\_ _ _ _ ops -> ops)

-- Update Operations

-- |update program
updTProg :: (String -> String) ->
            ([String] -> [String]) ->
            ([TypeDecl] -> [TypeDecl]) ->
            ([TFuncDecl] -> [TFuncDecl]) ->
            ([OpDecl] -> [OpDecl]) -> TProg -> TProg
updTProg fn fi ft ff fo = trTProg prog
 where
  prog name imps types funcs ops
    = TProg (fn name) (fi imps) (ft types) (ff funcs) (fo ops)

-- |update name of program
updTProgName :: Update TProg String
updTProgName f = updTProg f id id id id

-- |update imports of program
updTProgImports :: Update TProg [String]
updTProgImports f = updTProg id f id id id

-- |update type declarations of program
updTProgTypes :: Update TProg [TypeDecl]
updTProgTypes f = updTProg id id f id id

-- |update functions of program
updTProgTFuncs :: Update TProg [TFuncDecl]
updTProgTFuncs f = updTProg id id id f id

-- |update infix operators of program
updTProgOps :: Update TProg [OpDecl]
updTProgOps = updTProg id id id id

-- Auxiliary Functions

-- |get all program variables (also from patterns)
allVarsInTProg :: TProg -> [(VarIndex, TypeExpr)]
allVarsInTProg = concatMap allVarsInTFunc . tProgTFuncs

-- |lift transformation on expressions to program
updTProgTExps :: Update TProg TExpr
updTProgTExps = updTProgTFuncs . map . updTFuncBody

-- |rename programs variables
rnmAllVarsInTProg :: Update TProg VarIndex
rnmAllVarsInTProg = updTProgTFuncs . map . rnmAllVarsInTFunc

-- |update all qualified names in program
updQNamesInTProg :: Update TProg QName
updQNamesInTProg f = updTProg id id
  (map (updQNamesInType f)) (map (updQNamesInTFunc f)) (map (updOpName f))

-- |rename program (update name of and all qualified names in program)
rnmTProg :: String -> TProg -> TProg
rnmTProg name p = updTProgName (const name) (updQNamesInTProg rnm p)
 where
  rnm (m, n) | m == tProgName p = (name, n)
             | otherwise = (m, n)

-- TFuncDecl ------------------------------------------------------------------

-- |transform function
trTFunc :: (QName -> Int -> Visibility -> TypeExpr -> TRule -> b) -> TFuncDecl -> b
trTFunc func (TFunc name arity vis t rule) = func name arity vis t rule

-- Selectors

-- |get name of function
tFuncName :: TFuncDecl -> QName
tFuncName = trTFunc (\name _ _ _ _ -> name)

-- |get arity of function
tFuncArity :: TFuncDecl -> Int
tFuncArity = trTFunc (\_ arity _ _ _ -> arity)

-- |get visibility of function
tFuncVisibility :: TFuncDecl -> Visibility
tFuncVisibility = trTFunc (\_ _ vis _ _ -> vis)

-- |get type of function
tFuncType :: TFuncDecl -> TypeExpr
tFuncType = trTFunc (\_ _ _ t _ -> t)

-- |get rule of function
tFuncTRule :: TFuncDecl -> TRule
tFuncTRule = trTFunc (\_ _ _ _ rule -> rule)

-- Update Operations

-- |update function
updTFunc :: (QName -> QName) ->
            (Int -> Int) ->
            (Visibility -> Visibility) ->
            (TypeExpr -> TypeExpr) ->
            (TRule -> TRule) -> TFuncDecl -> TFuncDecl
updTFunc fn fa fv ft fr = trTFunc func
 where
  func name arity vis t rule
    = TFunc (fn name) (fa arity) (fv vis) (ft t) (fr rule)

-- |update name of function
updTFuncName :: Update TFuncDecl QName
updTFuncName f = updTFunc f id id id id

-- |update arity of function
updTFuncArity :: Update TFuncDecl Int
updTFuncArity f = updTFunc id f id id id

-- |update visibility of function
updTFuncVisibility :: Update TFuncDecl Visibility
updTFuncVisibility f = updTFunc id id f id id

-- |update type of function
updFuncType :: Update TFuncDecl TypeExpr
updFuncType f = updTFunc id id id f id

-- |update rule of function
updTFuncTRule :: Update TFuncDecl TRule
updTFuncTRule = updTFunc id id id id

-- Auxiliary Functions

-- |is function public?
isPublicTFunc :: TFuncDecl -> Bool
isPublicTFunc = isPublic . tFuncVisibility

-- |is function externally defined?
isExternal :: TFuncDecl -> Bool
isExternal = isTRuleExternal . tFuncTRule

-- |get variable names in a function declaration
allVarsInTFunc :: TFuncDecl -> [(VarIndex, TypeExpr)]
allVarsInTFunc = allVarsInTRule . tFuncTRule

-- |get arguments of function, if not externally defined
tFuncArgs :: TFuncDecl -> [(VarIndex, TypeExpr)]
tFuncArgs = tRuleArgs . tFuncTRule

-- |get body of function, if not externally defined
tFuncBody :: TFuncDecl -> TExpr
tFuncBody = tRuleBody . tFuncTRule

-- |get the right-hand-sides of a 'FuncDecl'
tFuncRHS :: TFuncDecl -> [TExpr]
tFuncRHS f | not (isExternal f) = orCase (tFuncBody f)
           | otherwise = []
 where
  orCase e
    | isTOr e = concatMap orCase (orExps e)
    | isTCase e = concatMap (orCase . tBranchTExpr) (caseBranches e)
    | otherwise = [e]

-- |rename all variables in function
rnmAllVarsInTFunc :: Update TFuncDecl VarIndex
rnmAllVarsInTFunc = updTFunc id id id id . rnmAllVarsInTRule

-- |update all qualified names in function
updQNamesInTFunc :: Update TFuncDecl QName
updQNamesInTFunc f = updTFunc f id id (updQNamesInTypeExpr f) (updQNamesInTRule f)

-- |update arguments of function, if not externally defined
updTFuncArgs :: Update TFuncDecl [(VarIndex, TypeExpr)]
updTFuncArgs = updTFuncTRule . updTRuleArgs

-- |update body of function, if not externally defined
updTFuncBody :: Update TFuncDecl TExpr
updTFuncBody = updTFuncTRule . updTRuleBody

-- TRule ----------------------------------------------------------------------

-- |transform rule
trTRule :: ([(VarIndex, TypeExpr)] -> TExpr -> b) -> (TypeExpr -> String -> b) -> TRule -> b
trTRule rule _ (TRule args e) = rule args e
trTRule _ ext (TExternal ty s) = ext ty s

-- Selectors

-- |get rules arguments if it's not external
tRuleArgs :: TRule -> [(VarIndex, TypeExpr)]
tRuleArgs = trTRule const undefined

-- |get rules body if it's not external
tRuleBody :: TRule -> TExpr
tRuleBody = trTRule (\_ e -> e) undefined

-- |get rules external declaration
tRuleExtDecl :: TRule -> String
tRuleExtDecl = trTRule undefined (\_ s -> s)

-- Test Operations

-- |is rule external?
isTRuleExternal :: TRule -> Bool
isTRuleExternal = trTRule (\_ _ -> False) (\_ _ -> True)

-- Update Operations

-- |update rule
updTRule :: (TypeExpr -> TypeExpr) ->
            ([(VarIndex, TypeExpr)] -> [(VarIndex, TypeExpr)]) ->
            (TExpr -> TExpr) ->
            (String -> String) -> TRule -> TRule
updTRule fannot fa fe fs = trTRule rule ext
 where
  rule args e = TRule (fa args) (fe e)
  ext ty s = TExternal (fannot ty) (fs s)

-- |update rules TypeExpr
updTRuleType :: Update TRule TypeExpr
updTRuleType f = updTRule f id id id

-- |update rules arguments
updTRuleArgs :: Update TRule [(VarIndex, TypeExpr)]
updTRuleArgs f = updTRule id f id id

-- |update rules body
updTRuleBody :: Update TRule TExpr
updTRuleBody f = updTRule id id f id

-- |update rules external declaration
updTRuleExtDecl :: Update TRule String
updTRuleExtDecl = updTRule id id id

-- Auxiliary Functions

-- |get variable names in a functions rule
allVarsInTRule :: TRule -> [(VarIndex, TypeExpr)]
allVarsInTRule = trTRule (\args body -> args ++ allVars body) (\_ _ -> [])

-- |rename all variables in rule
rnmAllVarsInTRule :: Update TRule VarIndex
rnmAllVarsInTRule f = updTRule id (map (first f)) (rnmAllVars f) id

-- |update all qualified names in rule
updQNamesInTRule :: Update TRule QName
updQNamesInTRule = updTRuleBody . updQNames

-- TExpr ----------------------------------------------------------------------

-- Selectors

-- |get internal number of variable
varNr :: TExpr -> VarIndex
varNr (TVarE _ n) = n
varNr _           = error "Curry.FlatCurry.Typed.Goodies.varNr: no variable"

-- |get literal if expression is literal expression
literal :: TExpr -> Literal
literal (TLit _ l) = l
literal _          = error "Curry.FlatCurry.Typed.Goodies.literal: no literal"

-- |get combination type of a combined expression
combType :: TExpr -> CombType
combType (TComb _ ct _ _) = ct
combType _                = error $ "Curry.FlatCurry.Typed.Goodies.combType: " ++
                                    "no combined expression"

-- |get name of a combined expression
combName :: TExpr -> QName
combName (TComb _ _ name _) = name
combName _                  = error $ "Curry.FlatCurry.Typed.Goodies.combName: " ++
                                      "no combined expression"

-- |get arguments of a combined expression
combArgs :: TExpr -> [TExpr]
combArgs (TComb _ _ _ args) = args
combArgs _                  = error $ "Curry.FlatCurry.Typed.Goodies.combArgs: " ++
                                      "no combined expression"

-- |get number of missing arguments if expression is combined
missingCombArgs :: TExpr -> Int
missingCombArgs = missingArgs . combType
  where
  missingArgs :: CombType -> Int
  missingArgs = trCombType 0 id 0 id

-- |get indices of variables in let declaration
letBinds :: TExpr -> [((VarIndex, TypeExpr), TExpr)]
letBinds (TLet vs _) = vs
letBinds _           = error $ "Curry.FlatCurry.Typed.Goodies.letBinds: " ++
                               "no let expression"

-- |get body of let declaration
letBody :: TExpr -> TExpr
letBody (TLet _ e) = e
letBody _          = error $ "Curry.FlatCurry.Typed.Goodies.letBody: " ++
                             "no let expression"

-- |get variable indices from declaration of free variables
freeVars :: TExpr -> [(VarIndex, TypeExpr)]
freeVars (TFree vs _) = vs
freeVars _            = error $ "Curry.FlatCurry.Typed.Goodies.freeVars: " ++
                                "no declaration of free variables"

-- |get expression from declaration of free variables
freeExpr :: TExpr -> TExpr
freeExpr (TFree _ e) = e
freeExpr _           = error $ "Curry.FlatCurry.Typed.Goodies.freeExpr: " ++
                               "no declaration of free variables"

-- |get expressions from or-expression
orExps :: TExpr -> [TExpr]
orExps (TOr e1 e2) = [e1, e2]
orExps _           = error $ "Curry.FlatCurry.Typed.Goodies.orExps: " ++
                             "no or expression"

-- |get case-type of case expression
caseType :: TExpr -> CaseType
caseType (TCase ct _ _) = ct
caseType _              = error $ "Curry.FlatCurry.Typed.Goodies.caseType: " ++
                                  "no case expression"

-- |get scrutinee of case expression
caseExpr :: TExpr -> TExpr
caseExpr (TCase _ e _) = e
caseExpr _             = error $ "Curry.FlatCurry.Typed.Goodies.caseExpr: " ++
                                   "no case expression"


-- |get branch expressions from case expression
caseBranches :: TExpr -> [TBranchExpr]
caseBranches (TCase _ _ bs) = bs
caseBranches _              = error "Curry.FlatCurry.Typed.Goodies.caseBranches: no case expression"

-- Test Operations

-- |is expression a variable?
isTVarE :: TExpr -> Bool
isTVarE e = case e of
  TVarE {} -> True
  _        -> False

-- |is expression a literal expression?
isTLit :: TExpr -> Bool
isTLit e = case e of
  TLit {} -> True
  _       -> False

-- |is expression combined?
isTComb :: TExpr -> Bool
isTComb e = case e of
  TComb {} -> True
  _        -> False

-- |is expression a let expression?
isTLet :: TExpr -> Bool
isTLet e = case e of
  TLet {} -> True
  _       -> False

-- |is expression a declaration of free variables?
isTFree :: TExpr -> Bool
isTFree e = case e of
  TFree {} -> True
  _        -> False

-- |is expression an or-expression?
isTOr :: TExpr -> Bool
isTOr e = case e of
  TOr {} -> True
  _      -> False

-- |is expression a case expression?
isTCase :: TExpr -> Bool
isTCase e = case e of
  TCase {} -> True
  _        -> False

-- |transform expression
trTExpr  :: (TypeExpr -> VarIndex -> b)
         -> (TypeExpr -> Literal -> b)
         -> (TypeExpr -> CombType -> QName -> [b] -> b)
         -> ([((VarIndex, TypeExpr), b)] -> b -> b)
         -> ([(VarIndex, TypeExpr)] -> b -> b)
         -> (b -> b -> b)
         -> (CaseType -> b -> [c] -> b)
         -> (TPattern -> b -> c)
         -> (b -> TypeExpr -> b)
         -> TExpr
         -> b
trTExpr var lit comb lt fr oR cas branch typed expr = case expr of
  TVarE ty n            -> var ty n
  TLit ty l             -> lit ty l
  TComb ty ct name args -> comb ty ct name (map f args)
  TLet bs e             -> lt (map (second f) bs) (f e)
  TFree vs e            -> fr vs (f e)
  TOr e1 e2             -> oR (f e1) (f e2)
  TCase ct e bs         -> cas ct (f e) (map (\ (TBranch p e') -> branch p (f e')) bs)
  TTyped e ty           -> typed (f e) ty
  where
  f = trTExpr var lit comb lt fr oR cas branch typed

-- |update all variables in given expression
updVars :: (TypeExpr -> VarIndex -> TExpr) -> TExpr -> TExpr
updVars var = trTExpr var TLit TComb TLet TFree TOr TCase TBranch TTyped

-- |update all literals in given expression
updLiterals :: (TypeExpr -> Literal -> TExpr) -> TExpr -> TExpr
updLiterals lit = trTExpr TVarE lit TComb TLet TFree TOr TCase TBranch TTyped

-- |update all combined expressions in given expression
updCombs :: (TypeExpr -> CombType -> QName -> [TExpr] -> TExpr) -> TExpr -> TExpr
updCombs comb = trTExpr TVarE TLit comb TLet TFree TOr TCase TBranch TTyped

-- |update all let expressions in given expression
updLets :: ([((VarIndex, TypeExpr), TExpr)] -> TExpr -> TExpr) -> TExpr -> TExpr
updLets lt = trTExpr TVarE TLit TComb lt TFree TOr TCase TBranch TTyped

-- |update all free declarations in given expression
updFrees :: ([(VarIndex, TypeExpr)] -> TExpr -> TExpr) -> TExpr -> TExpr
updFrees fr = trTExpr TVarE TLit TComb TLet fr TOr TCase TBranch TTyped

-- |update all or expressions in given expression
updOrs :: (TExpr -> TExpr -> TExpr) -> TExpr -> TExpr
updOrs oR = trTExpr TVarE TLit TComb TLet TFree oR TCase TBranch TTyped

-- |update all case expressions in given expression
updCases :: (CaseType -> TExpr -> [TBranchExpr] -> TExpr) -> TExpr -> TExpr
updCases cas = trTExpr TVarE TLit TComb TLet TFree TOr cas TBranch TTyped

-- |update all case branches in given expression
updBranches :: (TPattern -> TExpr -> TBranchExpr) -> TExpr -> TExpr
updBranches branch = trTExpr TVarE TLit TComb TLet TFree TOr TCase branch TTyped

-- |update all typed expressions in given expression
updTypeds :: (TExpr -> TypeExpr -> TExpr) -> TExpr -> TExpr
updTypeds = trTExpr TVarE TLit TComb TLet TFree TOr TCase TBranch

-- Auxiliary Functions

-- |is expression a call of a function where all arguments are provided?
isFuncCall :: TExpr -> Bool
isFuncCall e = isTComb e && isCombTypeFuncCall (combType e)

-- |is expression a partial function call?
isFuncPartCall :: TExpr -> Bool
isFuncPartCall e = isTComb e && isCombTypeFuncPartCall (combType e)

-- |is expression a call of a constructor?
isConsCall :: TExpr -> Bool
isConsCall e = isTComb e && isCombTypeConsCall (combType e)

-- |is expression a partial constructor call?
isConsPartCall :: TExpr -> Bool
isConsPartCall e = isTComb e && isCombTypeConsPartCall (combType e)

-- |is expression fully evaluated?
isGround :: TExpr -> Bool
isGround e
  = case e of
      TComb _ ConsCall _ args -> all isGround args
      _ -> isTLit e

-- |get all variables (also pattern variables) in expression
allVars :: TExpr -> [(VarIndex, TypeExpr)]
allVars e = trTExpr var lit comb lt fr (.) cas branch typ e []
 where
  var a v = (:) (v, a)
  lit = const (const id)
  comb _ _ _ = foldr (.) id
  lt bs e' = e' . foldr ((.) . (\(n,ns) -> (n:) . ns)) id bs
  fr vs e' = (vs++) . e'
  cas _ e' bs = e' . foldr (.) id bs
  branch pat e' = (args pat ++) . e'
  typ = const
  args pat | isConsPattern pat = tPatArgs pat
           | otherwise = []

-- |rename all variables (also in patterns) in expression
rnmAllVars :: Update TExpr VarIndex
rnmAllVars f = trTExpr var TLit TComb lt fr TOr TCase branch TTyped
 where
   var a = TVarE a . f
   lt = TLet . map (\((n, b), e) -> ((f n, b), e))
   fr = TFree . map (first f)
   branch = TBranch . updTPatArgs (map (first f))

-- |update all qualified names in expression
updQNames :: Update TExpr QName
updQNames f = trTExpr TVarE TLit comb TLet TFree TOr TCase branch TTyped
 where
  comb ty ct name = TComb ty ct (f name)
  branch = TBranch . updTPatCons f

-- TBranchExpr ----------------------------------------------------------------

-- |transform branch expression
trTBranch :: (TPattern -> TExpr -> b) -> TBranchExpr -> b
trTBranch branch (TBranch pat e) = branch pat e

-- Selectors

-- |get pattern from branch expression
tBranchTPattern :: TBranchExpr -> TPattern
tBranchTPattern = trTBranch const

-- |get expression from branch expression
tBranchTExpr :: TBranchExpr -> TExpr
tBranchTExpr = trTBranch (\_ e -> e)

-- Update Operations

-- |update branch expression
updTBranch :: (TPattern -> TPattern) -> (TExpr -> TExpr) -> TBranchExpr -> TBranchExpr
updTBranch fp fe = trTBranch branch
 where
  branch pat e = TBranch (fp pat) (fe e)

-- |update pattern of branch expression
updTBranchTPattern :: Update TBranchExpr TPattern
updTBranchTPattern f = updTBranch f id

-- |update expression of branch expression
updTBranchTExpr :: Update TBranchExpr TExpr
updTBranchTExpr = updTBranch id

-- TPattern -------------------------------------------------------------------

-- |transform pattern
trTPattern :: (TypeExpr -> QName -> [(VarIndex, TypeExpr)] -> b) -> (TypeExpr -> Literal -> b) -> TPattern -> b
trTPattern pat _ (TPattern ty name args) = pat ty name args
trTPattern _ lpat (TLPattern a l) = lpat a l

-- Selectors

-- |get name from constructor pattern
tPatCons :: TPattern -> QName
tPatCons = trTPattern (\_ name _ -> name) undefined

-- |get arguments from constructor pattern
tPatArgs :: TPattern -> [(VarIndex, TypeExpr)]
tPatArgs = trTPattern (\_ _ args -> args) undefined

-- |get literal from literal pattern
tPatLiteral :: TPattern -> Literal
tPatLiteral = trTPattern undefined (const id)

-- Test Operations

-- |is pattern a constructor pattern?
isConsPattern :: TPattern -> Bool
isConsPattern = trTPattern (\_ _ _ -> True) (\_ _ -> False)

-- Update Operations

-- |update pattern
updTPattern :: (TypeExpr -> TypeExpr) ->
               (QName -> QName) ->
               ([(VarIndex, TypeExpr)] -> [(VarIndex, TypeExpr)]) ->
               (Literal -> Literal) -> TPattern -> TPattern
updTPattern fannot fn fa fl = trTPattern pattern lpattern
 where
  pattern ty name args = TPattern (fannot ty) (fn name) (fa args)
  lpattern ty l = TLPattern (fannot ty) (fl l)

-- |update TypeExpr of pattern
updTPatType :: (TypeExpr -> TypeExpr) -> TPattern -> TPattern
updTPatType f = updTPattern f id id id

-- |update constructors name of pattern
updTPatCons :: (QName -> QName) -> TPattern -> TPattern
updTPatCons f = updTPattern id f id id

-- |update arguments of constructor pattern
updTPatArgs :: ([(VarIndex, TypeExpr)] -> [(VarIndex, TypeExpr)]) -> TPattern -> TPattern
updTPatArgs f = updTPattern id id f id

-- |update literal of pattern
updTPatLiteral :: (Literal -> Literal) -> TPattern -> TPattern
updTPatLiteral = updTPattern id id id

-- Auxiliary Functions

-- |build expression from pattern
tPatExpr :: TPattern -> TExpr
tPatExpr = trTPattern (\ty name -> TComb ty ConsCall name . map (uncurry (flip TVarE))) TLit
