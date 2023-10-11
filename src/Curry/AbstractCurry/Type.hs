{- |
    Module      :  $Header$
    Description :  Library to support meta-programming in Curry
    Copyright   :  Michael Hanus  , 2004
                   Martin Engelke , 2005
                   Björn Peemöller, 2015
                   Finn Teegen    , 2016
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This library contains a definition for representing Curry programs
    in Haskell by the type 'CurryProg' and I/O actions to read Curry programs
    and transform them into this abstract representation as well as
    write them to a file.

    Note that this defines a slightly new format for AbstractCurry
    in comparison to the first proposal of 2003.
-}
module Curry.AbstractCurry.Type
  ( CurryProg (..), MName, QName, CVisibility (..), CTVarIName
  , CDefaultDecl (..), CClassDecl (..), CInstanceDecl (..)
  , CTypeDecl (..), CConsDecl (..), CFieldDecl (..)
  , CConstraint, CContext (..), CTypeExpr (..), CQualTypeExpr (..)
  , COpDecl (..), CFixity (..), Arity, CFuncDecl (..), CDetType (..), CRhs (..), CRule (..)
  , CLocalDecl (..), CVarIName, CExpr (..), CCaseType (..), CStatement (..)
  , CPattern (..), CLiteral (..), CField, version
  ) where

-- ---------------------------------------------------------------------------
-- Abstract syntax
-- ---------------------------------------------------------------------------

-- |Current version of AbstractCurry
version :: String
version = "AbstractCurry 4.0"

-- |A module name.
type MName = String

-- |A qualified name.
-- In AbstractCurry all names are qualified to avoid name clashes.
-- The first component is the module name and the second component the
-- unqualified name as it occurs in the source program.
type QName = (MName, String)

-- |Data type to specify the visibility of various entities.
data CVisibility
  = Public    -- ^ exported entity
  | Private   -- ^ private entity
    deriving (Eq, Read, Show)

-- |A Curry module in the intermediate form. A value of this type has the form
-- @
-- CurryProg modname imports dfltdecl clsdecls instdecls typedecls funcdecls opdecls
-- @
-- where
-- [@modname@]   Name of this module
-- [@imports@]   List of modules names that are imported
-- [@dfltdecl@]  Optional default declaration
-- [@clsdecls@]  Class declarations
-- [@instdecls@] Instance declarations
-- [@typedecls@] Type declarations
-- [@funcdecls@] Function declarations
-- [@opdecls@]   Operator precedence declarations
data CurryProg = CurryProg MName [MName] (Maybe CDefaultDecl) [CClassDecl]
                           [CInstanceDecl] [CTypeDecl] [CFuncDecl] [COpDecl]
    deriving (Eq, Read, Show)

-- |Default declaration.
newtype CDefaultDecl = CDefaultDecl [CTypeExpr]
    deriving (Eq, Read, Show)

-- |Definitions of type classes.
-- A type class definition of the form
-- @
-- class cx => c a where { ...;f :: t;... }
-- @
-- is represented by the Curry term
-- @
-- (CClass c v cx tv [...(CFunc f ar v t [...,CRule r,...])...])
-- @
-- where @tv@ is the index of the type variable @a@ and @v@ is the
-- visibility of the type class resp. method.
-- /Note:/ The type variable indices are unique inside each class
--         declaration and are usually numbered from 0.
--         The methods' types share the type class' type variable index
--         as the class variable has to occur in a method's type signature.
--         The list of rules for a method's declaration may be empty if
--         no default implementation is provided. The arity @ar@ is
--         determined by a given default implementation or 0.
--         Regardless of whether typed or untyped abstract curry is generated,
--         the methods' declarations are always typed.
data CClassDecl = CClass QName CVisibility CContext CTVarIName [CFuncDecl]
    deriving (Eq, Read, Show)

-- |Definitions of instances.
-- An instance definition of the form
-- @
-- instance cx => c ty where { ...;fundecl;... }
-- @
-- is represented by the Curry term
-- @
-- (CInstance c cx ty [...fundecl...])
-- @
-- /Note:/ The type variable indices are unique inside each instance
--         declaration and are usually numbered from 0.
--         The methods' types use the instance's type variable indices
--         (if typed abstract curry is generated).
data CInstanceDecl = CInstance QName CContext CTypeExpr [CFuncDecl]
    deriving (Eq, Read, Show)

-- |Definitions of algebraic data types and type synonyms.
-- A data type definition of the form
-- @
-- data t x1...xn = ...| forall y1...ym . cx => c t1....tkc |...
--   deriving (d1,...,dp)
-- @
-- is represented by the Curry term
-- @
-- (CType t v [i1,...,in] [...(CCons [l1,...,lm] cx c kc v [t1,...,tkc])...]
--        [d1,...,dp])
-- @
-- where each @ij@ is the index of the type variable @xj@, each @lj@ is the
-- index of the existentially quantified type variable @yj@ and @v@ is the
-- visibility of the type resp. constructor.
-- /Note:/ The type variable indices are unique inside each type declaration
--         and are usually numbered from 0.
-- Thus, a data type declaration consists of the name of the data type,
-- a list of type parameters and a list of constructor declarations.
data CTypeDecl
    -- |algebraic data type
  = CType    QName CVisibility [CTVarIName] [CConsDecl] [QName]
    -- |type synonym
  | CTypeSyn QName CVisibility [CTVarIName] CTypeExpr
    -- |renaming type, may have only exactly one type expression
    -- in the constructor declaration and no existentially type variables and
    -- no context
  | CNewType QName CVisibility [CTVarIName] CConsDecl [QName]
    deriving (Eq, Read, Show)

-- |The type for representing type variables.
-- They are represented by @(i,n)@ where @i@ is a type variable index
-- which is unique inside a function and @n@ is a name (if possible,
-- the name written in the source program).
type CTVarIName = (Int, String)

-- |A constructor declaration consists of the name of the constructor
-- and a list of the argument types of the constructor.
-- The arity equals the number of types.
data CConsDecl
  = CCons   QName CVisibility [CTypeExpr]
  | CRecord QName CVisibility [CFieldDecl]
    deriving (Eq, Read, Show)

-- |A record field declaration consists of the name of the
-- the label, the visibility and its corresponding type.
data CFieldDecl = CField QName CVisibility CTypeExpr
  deriving (Eq, Read, Show)

-- |The type for representing a class constraint.
type CConstraint = (QName, CTypeExpr)

-- |The type for representing a context.
data CContext = CContext [CConstraint]
  deriving (Eq, Read, Show)

-- |Type expression.
-- A type expression is either a type variable, a function type,
-- a type constructor or a type application.
data CTypeExpr
    -- |Type variable
  = CTVar CTVarIName
    -- |Function type @t1 -> t2@
  | CFuncType CTypeExpr CTypeExpr
    -- |Type constructor
  | CTCons QName
    -- |Type application
  | CTApply CTypeExpr CTypeExpr
    deriving (Eq, Read, Show)

-- |Qualified type expression.
data CQualTypeExpr = CQualType CContext CTypeExpr
    deriving (Eq, Read, Show)

-- |Labeled record fields
type CField a = (QName, a)

-- |Operator precedence declaration.
-- An operator precedence declaration @fix p n@ in Curry corresponds to the
-- AbstractCurry term @(COp n fix p)@.
data COpDecl = COp QName CFixity Int
    deriving (Eq, Read, Show)

-- |Fixity declarations of infix operators
data CFixity
  = CInfixOp  -- ^ non-associative infix operator
  | CInfixlOp -- ^ left-associative infix operator
  | CInfixrOp -- ^ right-associative infix operator
    deriving (Eq, Read, Show)

-- |Function arity
type Arity = Int

-- |Data type for representing function declarations.
-- A function declaration in FlatCurry is a term of the form
-- @
-- (CFunc name arity visibility type dtype (CRules eval [CRule rule1,...,rulek]))
-- @
-- and represents the function @name@ with definition
-- @
-- name :? dtype
-- name :: type
-- rule1
-- ...
-- rulek
-- @
-- /Note:/ The variable indices are unique inside each rule.
-- External functions are represented as
-- @
-- (CFunc name arity type dtype (CExternal s))
-- @
-- where s is the external name associated to this function.
-- Thus, a function declaration consists of the name, arity, type, and
-- a list of rules.
-- If the list of rules is empty, the function is considered
-- to be externally defined.
data CFuncDecl = CFunc QName Arity CVisibility CQualTypeExpr CDetType [CRule]
    deriving (Eq, Read, Show)

-- |Determinism type
-- A determinism type describes how a function behaves w.r.t nondeterminism.
-- A function with determinism type @ a1 -> ... -> Det @
-- is guaranteed to be deterministic when the input provided to the function
-- has the required types @a1 ... an-1@.
-- If the type of the arguments does not match, the function might produce
-- nondeterministic results.
-- A determinism type can either be deterministic (@CDet@),
-- nondeterministic (@CAny@),
-- a type variable (@CDetVar@) to allow "determiminism polymorphism"
-- or a function type (@CDetArrow@).
data CDetType
  = CDet
  | CAny
  | CDetVar CTVarIName
  | CDetArrow  CDetType CDetType
  deriving (Eq, Read, Show)

-- |The general form of a function rule. It consists of a list of patterns
-- (left-hand side), a list of guards (@success@ if not present in the
-- source text) with their corresponding right-hand sides, and
-- a list of local declarations.
data CRule = CRule [CPattern] CRhs
    deriving (Eq, Read, Show)

-- |Right-hand-side of a 'CRule' or an @case@ expression
data CRhs
  = CSimpleRhs  CExpr            [CLocalDecl] -- @expr where decls@
  | CGuardedRhs [(CExpr, CExpr)] [CLocalDecl] -- @| cond = expr where decls@
    deriving (Eq, Read, Show)

-- | Local (let/where) declarations
data CLocalDecl
  = CLocalFunc CFuncDecl     -- ^ local function declaration
  | CLocalPat  CPattern CRhs -- ^ local pattern declaration
  | CLocalVars [CVarIName]   -- ^ local free variable declarations
    deriving (Eq, Read, Show)

-- |Variable names.
-- Object variables occurring in expressions are represented by @(Var i)@
-- where @i@ is a variable index.
type CVarIName = (Int, String)

-- |Pattern expressions.
data CPattern
    -- |pattern variable (unique index / name)
  = CPVar CVarIName
    -- |literal (Integer/Float/Char constant)
  | CPLit CLiteral
    -- |application @(m.c e1 ... en)@ of n-ary constructor @m.c@
    --  (@CPComb (m,c) [e1,...,en]@)
  | CPComb QName [CPattern]
    -- |as-pattern (extended Curry)
  | CPAs CVarIName CPattern
    -- |functional pattern (extended Curry)
  | CPFuncComb QName [CPattern]
    -- |lazy pattern (extended Curry)
  | CPLazy CPattern
    -- |record pattern (extended curry)
  | CPRecord QName [CField CPattern]
    deriving (Eq, Read, Show)

-- | Curry expressions.
data CExpr
    -- |variable (unique index / name)
  = CVar       CVarIName
    -- |literal (Integer/Float/Char/String constant)
  | CLit       CLiteral
    -- |a defined symbol with module and name, i.e., a function or a constructor
  | CSymbol    QName
    -- |application (e1 e2)
  | CApply     CExpr CExpr
    -- |lambda abstraction
  | CLambda    [CPattern] CExpr
    -- |local let declarations
  | CLetDecl   [CLocalDecl] CExpr
    -- |do block
  | CDoExpr    [CStatement]
    -- |list comprehension
  | CListComp  CExpr [CStatement]
    -- |case expression
  | CCase      CCaseType CExpr [(CPattern, CRhs)]
    -- |typed expression
  | CTyped     CExpr CQualTypeExpr
    -- |record construction (extended Curry)
  | CRecConstr QName [CField CExpr]
    -- |record update (extended Curry)
  | CRecUpdate CExpr [CField CExpr]
    deriving (Eq, Read, Show)

-- |Literals occurring in an expression or a pattern,
-- either an integer, a float, a character, or a string constant.
-- /Note:/ The constructor definition of 'CIntc' differs from the original
-- PAKCS definition. It uses Haskell type 'Integer' instead of 'Int'
-- to provide an unlimited range of integer numbers. Furthermore,
-- float values are represented with Haskell type 'Double' instead of
-- 'Float' to gain double precision.
data CLiteral
  = CIntc    Integer -- ^ Int literal
  | CFloatc  Double  -- ^ Float literal
  | CCharc   Char    -- ^ Char literal
  | CStringc String  -- ^ String literal
    deriving (Eq, Read, Show)

-- |Statements in do expressions and list comprehensions.
data CStatement
  = CSExpr CExpr          -- ^ an expression (I/O action or boolean)
  | CSPat  CPattern CExpr -- ^ a pattern definition
  | CSLet  [CLocalDecl]   -- ^ a local let declaration
    deriving (Eq, Read, Show)

-- |Type of case expressions
data CCaseType
  = CRigid -- ^ rigid case expression
  | CFlex  -- ^ flexible case expression
    deriving (Eq, Read, Show)
