{- |
    Module      : $Header$
    Description : Utility functions for working with annotated FlatCurry.
    Copyright   : (c) 2016 - 2017 Finn Teegen
    License     : BSD-3-clause

    Maintainer  : fte@informatik.uni-kiel.de
    Stability   : experimental
    Portability : portable

    This library provides selector functions, test and update operations
    as well as some useful auxiliary functions for AnnotatedFlatCurry data terms.
    Most of the provided functions are based on general transformation
    functions that replace constructors with user-defined
    functions. For recursive datatypes the transformations are defined
    inductively over the term structure. This is quite usual for
    transformations on AnnotatedFlatCurry terms,
    so the provided functions can be used to implement specific transformations
    without having to explicitly state the recursion. Essentially, the tedious
    part of such transformations - descend in fairly complex term structures -
    is abstracted away, which hopefully makes the code more clear and brief.
-}

module Curry.FlatCurry.Annotated.Goodies
  ( module Curry.FlatCurry.Annotated.Goodies
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

import Curry.FlatCurry.Annotated.Type

-- AProg ----------------------------------------------------------------------

-- |transform program
trAProg :: (String -> [String] -> [TypeDecl] -> [AFuncDecl a] -> [OpDecl] -> b)
        -> AProg a -> b
trAProg prog (AProg name imps types funcs ops) = prog name imps types funcs ops

-- Selectors

-- |get name from program
aProgName :: AProg a -> String
aProgName = trAProg (\name _ _ _ _ -> name)

-- |get imports from program
aProgImports :: AProg a -> [String]
aProgImports = trAProg (\_ imps _ _ _ -> imps)

-- |get type declarations from program
aProgTypes :: AProg a -> [TypeDecl]
aProgTypes = trAProg (\_ _ types _ _ -> types)

-- |get functions from program
aProgAFuncs :: AProg a -> [AFuncDecl a]
aProgAFuncs = trAProg (\_ _ _ funcs _ -> funcs)

-- |get infix operators from program
aProgOps :: AProg a -> [OpDecl]
aProgOps = trAProg (\_ _ _ _ ops -> ops)

-- Update Operations

-- |update program
updAProg :: (String -> String) ->
            ([String] -> [String]) ->
            ([TypeDecl] -> [TypeDecl]) ->
            ([AFuncDecl a] -> [AFuncDecl a]) ->
            ([OpDecl] -> [OpDecl]) -> AProg a -> AProg a
updAProg fn fi ft ff fo = trAProg prog
 where
  prog name imps types funcs ops
    = AProg (fn name) (fi imps) (ft types) (ff funcs) (fo ops)

-- |update name of program
updAProgName :: Update (AProg a) String
updAProgName f = updAProg f id id id id

-- |update imports of program
updAProgImports :: Update (AProg a) [String]
updAProgImports f = updAProg id f id id id

-- |update type declarations of program
updAProgTypes :: Update (AProg a) [TypeDecl]
updAProgTypes f = updAProg id id f id id

-- |update functions of program
updAProgAFuncs :: Update (AProg a) [AFuncDecl a]
updAProgAFuncs f = updAProg id id id f id

-- |update infix operators of program
updAProgOps :: Update (AProg a) [OpDecl]
updAProgOps = updAProg id id id id

-- Auxiliary Functions

-- |get all program variables (also from patterns)
allVarsInAProg :: AProg a -> [(VarIndex, a)]
allVarsInAProg = concatMap allVarsInAFunc . aProgAFuncs

-- |lift transformation on expressions to program
updAProgAExps :: Update (AProg a) (AExpr a)
updAProgAExps = updAProgAFuncs . map . updAFuncBody

-- |rename programs variables
rnmAllVarsInAProg :: Update (AProg a) VarIndex
rnmAllVarsInAProg = updAProgAFuncs . map . rnmAllVarsInAFunc

-- |update all qualified names in program
updQNamesInAProg :: Update (AProg a) QName
updQNamesInAProg f = updAProg id id
  (map (updQNamesInType f)) (map (updQNamesInAFunc f)) (map (updOpName f))

-- |rename program (update name of and all qualified names in program)
rnmAProg :: String -> AProg a -> AProg a
rnmAProg name p = updAProgName (const name) (updQNamesInAProg rnm p)
 where
  rnm (m, n) | m == aProgName p = (name, n)
             | otherwise = (m, n)

-- AFuncDecl ------------------------------------------------------------------

-- |transform function
trAFunc :: (QName -> Int -> Visibility -> TypeExpr -> ARule a -> b) -> AFuncDecl a -> b
trAFunc func (AFunc name arity vis t rule) = func name arity vis t rule

-- Selectors

-- |get name of function
aFuncName :: AFuncDecl a -> QName
aFuncName = trAFunc (\name _ _ _ _ -> name)

-- |get arity of function
aFuncArity :: AFuncDecl a -> Int
aFuncArity = trAFunc (\_ arity _ _ _ -> arity)

-- |get visibility of function
aFuncVisibility :: AFuncDecl a -> Visibility
aFuncVisibility = trAFunc (\_ _ vis _ _ -> vis)

-- |get type of function
aFuncType :: AFuncDecl a -> TypeExpr
aFuncType = trAFunc (\_ _ _ t _ -> t)

-- |get rule of function
aFuncARule :: AFuncDecl a -> ARule a
aFuncARule = trAFunc (\_ _ _ _ rule -> rule)

-- Update Operations

-- |update function
updAFunc :: (QName -> QName) ->
            (Int -> Int) ->
            (Visibility -> Visibility) ->
            (TypeExpr -> TypeExpr) ->
            (ARule a -> ARule a) -> AFuncDecl a -> AFuncDecl a
updAFunc fn fa fv ft fr = trAFunc func
 where
  func name arity vis t rule
    = AFunc (fn name) (fa arity) (fv vis) (ft t) (fr rule)

-- |update name of function
updAFuncName :: Update (AFuncDecl a) QName
updAFuncName f = updAFunc f id id id id

-- |update arity of function
updAFuncArity :: Update (AFuncDecl a) Int
updAFuncArity f = updAFunc id f id id id

-- |update visibility of function
updAFuncVisibility :: Update (AFuncDecl a) Visibility
updAFuncVisibility f = updAFunc id id f id id

-- |update type of function
updFuncType :: Update (AFuncDecl a) TypeExpr
updFuncType f = updAFunc id id id f id

-- |update rule of function
updAFuncARule :: Update (AFuncDecl a) (ARule a)
updAFuncARule = updAFunc id id id id

-- Auxiliary Functions

-- |is function public?
isPublicAFunc :: AFuncDecl a -> Bool
isPublicAFunc = isPublic . aFuncVisibility

-- |is function externally defined?
isExternal :: AFuncDecl a -> Bool
isExternal = isARuleExternal . aFuncARule

-- |get variable names in a function declaration
allVarsInAFunc :: AFuncDecl a -> [(VarIndex, a)]
allVarsInAFunc = allVarsInARule . aFuncARule

-- |get arguments of function, if not externally defined
aFuncArgs :: AFuncDecl a -> [(VarIndex, a)]
aFuncArgs = aRuleArgs . aFuncARule

-- |get body of function, if not externally defined
aFuncBody :: AFuncDecl a -> AExpr a
aFuncBody = aRuleBody . aFuncARule

-- |get the right-hand-sides of a 'FuncDecl'
aFuncRHS :: AFuncDecl a -> [AExpr a]
aFuncRHS f | not (isExternal f) = orCase (aFuncBody f)
           | otherwise = []
 where
  orCase e
    | isAOr e = concatMap orCase (orExps e)
    | isACase e = concatMap (orCase . aBranchAExpr) (caseBranches e)
    | otherwise = [e]

-- |rename all variables in function
rnmAllVarsInAFunc :: Update (AFuncDecl a) VarIndex
rnmAllVarsInAFunc = updAFunc id id id id . rnmAllVarsInARule

-- |update all qualified names in function
updQNamesInAFunc :: Update (AFuncDecl a) QName
updQNamesInAFunc f = updAFunc f id id (updQNamesInTypeExpr f) (updQNamesInARule f)

-- |update arguments of function, if not externally defined
updAFuncArgs :: Update (AFuncDecl a) [(VarIndex, a)]
updAFuncArgs = updAFuncARule . updARuleArgs

-- |update body of function, if not externally defined
updAFuncBody :: Update (AFuncDecl a) (AExpr a)
updAFuncBody = updAFuncARule . updARuleBody

-- ARule ----------------------------------------------------------------------

-- |transform rule
trARule :: (a -> [(VarIndex, a)] -> AExpr a -> b) -> (a -> String -> b) -> ARule a -> b
trARule rule _ (ARule a args e) = rule a args e
trARule _ ext (AExternal a s) = ext a s

-- Selectors

-- |get rules annotation
aRuleAnnot :: ARule a -> a
aRuleAnnot = trARule (\a _ _ -> a) const

-- |get rules arguments if it's not external
aRuleArgs :: ARule a -> [(VarIndex, a)]
aRuleArgs = trARule (\_ args _ -> args) undefined

-- |get rules body if it's not external
aRuleBody :: ARule a -> AExpr a
aRuleBody = trARule (\_ _ e -> e) undefined

-- |get rules external declaration
aRuleExtDecl :: ARule a -> String
aRuleExtDecl = trARule undefined (\_ s -> s)

-- Test Operations

-- |is rule external?
isARuleExternal :: ARule a -> Bool
isARuleExternal = trARule (\_ _ _ -> False) (\_ _ -> True)

-- Update Operations

-- |update rule
updARule :: (a -> b) ->
            ([(VarIndex, a)] -> [(VarIndex, b)]) ->
            (AExpr a -> AExpr b) ->
            (String -> String) -> ARule a -> ARule b
updARule fannot fa fe fs = trARule rule ext
 where
  rule a args e = ARule (fannot a) (fa args) (fe e)
  ext a s = AExternal (fannot a) (fs s)

-- |update rules annotation
updARuleAnnot :: Update (ARule a) a
updARuleAnnot f = updARule f id id id

-- |update rules arguments
updARuleArgs :: Update (ARule a) [(VarIndex, a)]
updARuleArgs f = updARule id f id id

-- |update rules body
updARuleBody :: Update (ARule a) (AExpr a)
updARuleBody f = updARule id id f id

-- |update rules external declaration
updARuleExtDecl :: Update (ARule a) String
updARuleExtDecl = updARule id id id

-- Auxiliary Functions

-- |get variable names in a functions rule
allVarsInARule :: ARule a -> [(VarIndex, a)]
allVarsInARule = trARule (\_ args body -> args ++ allVars body) (\_ _ -> [])

-- |rename all variables in rule
rnmAllVarsInARule :: Update (ARule a) VarIndex
rnmAllVarsInARule f = updARule id (map (first f)) (rnmAllVars f) id

-- |update all qualified names in rule
updQNamesInARule :: Update (ARule a) QName
updQNamesInARule = updARuleBody . updQNames

-- AExpr ----------------------------------------------------------------------

-- Selectors

-- |get annoation of an expression
annot :: AExpr a -> a
annot (AVar   a _    ) = a
annot (ALit   a _    ) = a
annot (AComb  a _ _ _) = a
annot (ALet   a _ _  ) = a
annot (AFree  a _ _  ) = a
annot (AOr    a _ _  ) = a
annot (ACase  a _ _ _) = a
annot (ATyped a _ _  ) = a

-- |get internal number of variable
varNr :: AExpr a -> VarIndex
varNr (AVar _ n) = n
varNr _          = error "Curry.FlatCurry.Annotated.Goodies.varNr: no variable"

-- |get literal if expression is literal expression
literal :: AExpr a -> Literal
literal (ALit _ l) = l
literal _          = error "Curry.FlatCurry.Annotated.Goodies.literal: no literal"

-- |get combination type of a combined expression
combType :: AExpr a -> CombType
combType (AComb _ ct _ _) = ct
combType _                = error $ "Curry.FlatCurry.Annotated.Goodies.combType: " ++
                                    "no combined expression"

-- |get name of a combined expression
combName :: AExpr a -> (QName, a)
combName (AComb _ _ name _) = name
combName _                  = error $ "Curry.FlatCurry.Annotated.Goodies.combName: " ++
                                      "no combined expression"

-- |get arguments of a combined expression
combArgs :: AExpr a -> [AExpr a]
combArgs (AComb _ _ _ args) = args
combArgs _                  = error $ "Curry.FlatCurry.Annotated.Goodies.combArgs: " ++
                                      "no combined expression"

-- |get number of missing arguments if expression is combined
missingCombArgs :: AExpr a -> Int
missingCombArgs = missingArgs . combType
  where
  missingArgs :: CombType -> Int
  missingArgs = trCombType 0 id 0 id

-- |get indices of varoables in let declaration
letBinds :: AExpr a -> [((VarIndex, a), AExpr a)]
letBinds (ALet _ vs _) = vs
letBinds _             = error $ "Curry.FlatCurry.Annotated.Goodies.letBinds: " ++
                                 "no let expression"

-- |get body of let declaration
letBody :: AExpr a -> AExpr a
letBody (ALet _ _ e) = e
letBody _            = error $ "Curry.FlatCurry.Annotated.Goodies.letBody: " ++
                               "no let expression"

-- |get variable indices from declaration of free variables
freeVars :: AExpr a -> [(VarIndex, a)]
freeVars (AFree _ vs _) = vs
freeVars _              = error $ "Curry.FlatCurry.Annotated.Goodies.freeVars: " ++
                                  "no declaration of free variables"

-- |get expression from declaration of free variables
freeExpr :: AExpr a -> AExpr a
freeExpr (AFree _ _ e) = e
freeExpr _             = error $ "Curry.FlatCurry.Annotated.Goodies.freeExpr: " ++
                                 "no declaration of free variables"

-- |get expressions from or-expression
orExps :: AExpr a -> [AExpr a]
orExps (AOr _ e1 e2) = [e1, e2]
orExps _             = error $ "Curry.FlatCurry.Annotated.Goodies.orExps: " ++
                               "no or expression"

-- |get case-type of case expression
caseType :: AExpr a -> CaseType
caseType (ACase _ ct _ _) = ct
caseType _                = error $ "Curry.FlatCurry.Annotated.Goodies.caseType: " ++
                                    "no case expression"

-- |get scrutinee of case expression
caseExpr :: AExpr a -> AExpr a
caseExpr (ACase _ _ e _) = e
caseExpr _               = error $ "Curry.FlatCurry.Annotated.Goodies.caseExpr: " ++
                                   "no case expression"


-- |get branch expressions from case expression
caseBranches :: AExpr a -> [ABranchExpr a]
caseBranches (ACase _ _ _ bs) = bs
caseBranches _                = error
  "Curry.FlatCurry.Annotated.Goodies.caseBranches: no case expression"

-- Test Operations

-- |is expression a variable?
isAVar :: AExpr a -> Bool
isAVar e = case e of
  AVar {} -> True
  _       -> False

-- |is expression a literal expression?
isALit :: AExpr a -> Bool
isALit e = case e of
  ALit {} -> True
  _       -> False

-- |is expression combined?
isAComb :: AExpr a -> Bool
isAComb e = case e of
  AComb { } -> True
  _         -> False

-- |is expression a let expression?
isALet :: AExpr a -> Bool
isALet e = case e of
  ALet {} -> True
  _       -> False

-- |is expression a declaration of free variables?
isAFree :: AExpr a -> Bool
isAFree e = case e of
  AFree{} -> True
  _       -> False

-- |is expression an or-expression?
isAOr :: AExpr a -> Bool
isAOr e = case e of
  AOr {} -> True
  _      -> False

-- |is expression a case expression?
isACase :: AExpr a -> Bool
isACase e = case e of
  ACase {} -> True
  _        -> False

-- |transform expression
trAExpr  :: (a -> VarIndex -> b)
         -> (a -> Literal -> b)
         -> (a -> CombType -> (QName, a) -> [b] -> b)
         -> (a -> [((VarIndex, a), b)] -> b -> b)
         -> (a -> [(VarIndex, a)] -> b -> b)
         -> (a -> b -> b -> b)
         -> (a -> CaseType -> b -> [c] -> b)
         -> (APattern a -> b -> c)
         -> (a -> b -> TypeExpr -> b)
         -> AExpr a
         -> b
trAExpr var lit comb lt fr oR cas branch typed expr = case expr of
  AVar a n             -> var a n
  ALit a l             -> lit a l
  AComb a ct name args -> comb a ct name (map f args)
  AFree a vs e         -> fr a vs (f e)
  ALet a bs e          -> lt a (map (second f) bs) (f e)
  AOr a e1 e2          -> oR a (f e1) (f e2)
  ACase a ct e bs      -> cas a ct (f e) (map (\ (ABranch p e') -> branch p (f e')) bs)
  ATyped a e ty        -> typed a (f e) ty
  where
  f = trAExpr var lit comb lt fr oR cas branch typed

-- |update all variables in given expression
updVars :: (a -> VarIndex -> AExpr a) -> AExpr a -> AExpr a
updVars var = trAExpr var ALit AComb ALet AFree AOr ACase ABranch ATyped

-- |update all literals in given expression
updLiterals :: (a -> Literal -> AExpr a) -> AExpr a -> AExpr a
updLiterals lit = trAExpr AVar lit AComb ALet AFree AOr ACase ABranch ATyped

-- |update all combined expressions in given expression
updCombs :: (a -> CombType -> (QName, a) -> [AExpr a] -> AExpr a) -> AExpr a -> AExpr a
updCombs comb = trAExpr AVar ALit comb ALet AFree AOr ACase ABranch ATyped

-- |update all let expressions in given expression
updLets :: (a -> [((VarIndex, a), AExpr a)] -> AExpr a -> AExpr a) -> AExpr a -> AExpr a
updLets lt = trAExpr AVar ALit AComb lt AFree AOr ACase ABranch ATyped

-- |update all free declarations in given expression
updFrees :: (a -> [(VarIndex, a)] -> AExpr a -> AExpr a) -> AExpr a -> AExpr a
updFrees fr = trAExpr AVar ALit AComb ALet fr AOr ACase ABranch ATyped

-- |update all or expressions in given expression
updOrs :: (a -> AExpr a -> AExpr a -> AExpr a) -> AExpr a -> AExpr a
updOrs oR = trAExpr AVar ALit AComb ALet AFree oR ACase ABranch ATyped

-- |update all case expressions in given expression
updCases :: (a -> CaseType -> AExpr a -> [ABranchExpr a] -> AExpr a) -> AExpr a -> AExpr a
updCases cas = trAExpr AVar ALit AComb ALet AFree AOr cas ABranch ATyped

-- |update all case branches in given expression
updBranches :: (APattern a -> AExpr a -> ABranchExpr a) -> AExpr a -> AExpr a
updBranches branch = trAExpr AVar ALit AComb ALet AFree AOr ACase branch ATyped

-- |update all typed expressions in given expression
updTypeds :: (a -> AExpr a -> TypeExpr -> AExpr a) -> AExpr a -> AExpr a
updTypeds = trAExpr AVar ALit AComb ALet AFree AOr ACase ABranch

-- Auxiliary Functions

-- |is expression a call of a function where all arguments are provided?
isFuncCall :: AExpr a -> Bool
isFuncCall e = isAComb e && isCombTypeFuncCall (combType e)

-- |is expression a partial function call?
isFuncPartCall :: AExpr a -> Bool
isFuncPartCall e = isAComb e && isCombTypeFuncPartCall (combType e)

-- |is expression a call of a constructor?
isConsCall :: AExpr a -> Bool
isConsCall e = isAComb e && isCombTypeConsCall (combType e)

-- |is expression a partial constructor call?
isConsPartCall :: AExpr a -> Bool
isConsPartCall e = isAComb e && isCombTypeConsPartCall (combType e)

-- |is expression fully evaluated?
isGround :: AExpr a -> Bool
isGround e
  = case e of
      AComb _ ConsCall _ args -> all isGround args
      _ -> isALit e

-- |get all variables (also pattern variables) in expression
allVars :: AExpr a -> [(VarIndex, a)]
allVars e = trAExpr var lit comb lt fr (const (.)) cas branch typ e []
 where
  var a v = (:) (v, a)
  lit = const (const id)
  comb _ _ _ = foldr (.) id
  lt _ bs e' = e' . foldr ((.) . (\(n,ns) -> (n:) . ns)) id bs
  fr _ vs e' = (vs++) . e'
  cas _ _ e' bs = e' . foldr (.) id bs
  branch pat e' = (args pat++) . e'
  typ _ = const
  args pat | isConsPattern pat = aPatArgs pat
           | otherwise = []

-- |rename all variables (also in patterns) in expression
rnmAllVars :: Update (AExpr a) VarIndex
rnmAllVars f = trAExpr var ALit AComb lt fr AOr ACase branch ATyped
 where
   var a = AVar a . f
   lt a = ALet a . map (\((n, b), e) -> ((f n, b), e))
   fr a = AFree a . map (first f)
   branch = ABranch . updAPatArgs (map (first f))

-- |update all qualified names in expression
updQNames :: Update (AExpr a) QName
updQNames f = trAExpr AVar ALit comb ALet AFree AOr ACase branch ATyped
 where
  comb a ct (name, a') = AComb a ct (f name, a')
  branch = ABranch . updAPatCons (first f)

-- ABranchExpr ----------------------------------------------------------------

-- |transform branch expression
trABranch :: (APattern a -> AExpr a -> b) -> ABranchExpr a -> b
trABranch branch (ABranch pat e) = branch pat e

-- Selectors

-- |get pattern from branch expression
aBranchAPattern :: ABranchExpr a -> APattern a
aBranchAPattern = trABranch const

-- |get expression from branch expression
aBranchAExpr :: ABranchExpr a -> AExpr a
aBranchAExpr = trABranch (\_ e -> e)

-- Update Operations

-- |update branch expression
updABranch :: (APattern a -> APattern a) -> (AExpr a -> AExpr a) -> ABranchExpr a -> ABranchExpr a
updABranch fp fe = trABranch branch
 where
  branch pat e = ABranch (fp pat) (fe e)

-- |update pattern of branch expression
updABranchAPattern :: Update (ABranchExpr a) (APattern a)
updABranchAPattern f = updABranch f id

-- |update expression of branch expression
updABranchAExpr :: Update (ABranchExpr a) (AExpr a)
updABranchAExpr = updABranch id

-- APattern -------------------------------------------------------------------

-- |transform pattern
trAPattern :: (a -> (QName, a) -> [(VarIndex, a)] -> b) -> (a -> Literal -> b) -> APattern a -> b
trAPattern pat _ (APattern a name args) = pat a name args
trAPattern _ lpat (ALPattern a l) = lpat a l

-- Selectors

-- |get annotation from pattern
aPatAnnot :: APattern a -> a
aPatAnnot = trAPattern (\a _ _ -> a) const

-- |get name from constructor pattern
aPatCons :: APattern a -> (QName, a)
aPatCons = trAPattern (\_ name _ -> name) undefined

-- |get arguments from constructor pattern
aPatArgs :: APattern a -> [(VarIndex, a)]
aPatArgs = trAPattern (\_ _ args -> args) undefined

-- |get literal from literal pattern
aPatLiteral :: APattern a -> Literal
aPatLiteral = trAPattern undefined (const id)

-- Test Operations

-- |is pattern a constructor pattern?
isConsPattern :: APattern a -> Bool
isConsPattern = trAPattern (\_ _ _ -> True) (\_ _ -> False)

-- Update Operations

-- |update pattern
updAPattern :: (a -> a) ->
               ((QName, a) -> (QName, a)) ->
               ([(VarIndex, a)] -> [(VarIndex, a)]) ->
               (Literal -> Literal) -> APattern a -> APattern a
updAPattern fannot fn fa fl = trAPattern pat lpat
 where
  pat a name args = APattern (fannot a) (fn name) (fa args)
  lpat a l = ALPattern (fannot a) (fl l)

-- |update annotation of pattern
updAPatAnnot :: (a -> a) -> APattern a -> APattern a
updAPatAnnot f = updAPattern f id id id

-- |update constructors name of pattern
updAPatCons :: ((QName, a) -> (QName, a)) -> APattern a -> APattern a
updAPatCons f = updAPattern id f id id

-- |update arguments of constructor pattern
updAPatArgs :: ([(VarIndex, a)] -> [(VarIndex, a)]) -> APattern a -> APattern a
updAPatArgs f = updAPattern id id f id

-- |update literal of pattern
updAPatLiteral :: (Literal -> Literal) -> APattern a -> APattern a
updAPatLiteral = updAPattern id id id

-- Auxiliary Functions

-- |build expression from pattern
aPatExpr :: APattern a -> AExpr a
aPatExpr = trAPattern (\a name -> AComb a ConsCall name . map (uncurry (flip AVar))) ALit
