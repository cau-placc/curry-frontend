{- |
    Module      :  $Header$
    Description :  Identifiers
    Copyright   :  (c) 1999 - 2004, Wolfgang Lux
                       2011 - 2013, Björn Peemöller
                       2016       , Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the implementation of identifiers and some
    utility functions for identifiers.

    Identifiers comprise the name of the denoted entity and an /id/,
    which can be used for renaming identifiers, e.g., in order to resolve
    name conflicts between identifiers from different scopes. An
    identifier with an /id/ @0@ is considered as not being renamed
    and, hence, its /id/ will not be shown.

    Qualified identifiers may optionally be prefixed by a module name.
-}
{-# LANGUAGE CPP            #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
module Curry.Base.Ident
  ( -- * Module identifiers
    ModuleIdent (..), mkMIdent, moduleName, escModuleName
  , fromModuleName, isValidModuleName, addPositionModuleIdent, mIdentLength

    -- * Local identifiers
  , Ident (..), mkIdent, showIdent, escName, identSupply
  , globalScope, hasGlobalScope, isRenamed, renameIdent, unRenameIdent
  , updIdentName, addPositionIdent, isInfixOp, identLength

    -- * Qualified identifiers
  , QualIdent (..), qualName, escQualName, isQInfixOp, qualify
  , qualifyWith, qualQualify, qualifyLike, isQualified, unqualify, qualUnqualify
  , localIdent, isLocalIdent, updQualIdent, qIdentLength

    -- * Predefined simple identifiers
    -- ** Identifiers for modules
  , emptyMIdent, mainMIdent, preludeMIdent
    -- ** Identifiers for types
  , arrowId, unitId, boolId, charId, intId, floatId, listId, ioId, successId
    -- ** Identifiers for type classes
  , eqId, ordId, enumId, boundedId, readId, showId
  , numId, fractionalId
  , monadId, monadFailId
  , dataId
    -- ** Identifiers for constructors
  , trueId, falseId, nilId, consId, tupleId, isTupleId, tupleArity
    -- ** Identifiers for values
  , mainId, minusId, fminusId, applyId, errorId, failedId, idId
  , succId, predId, toEnumId, fromEnumId, enumFromId, enumFromThenId
  , enumFromToId, enumFromThenToId
  , maxBoundId, minBoundId
  , lexId, readsPrecId, readParenId
  , showsPrecId, showParenId, showStringId
  , andOpId, eqOpId, leqOpId, ltOpId, orOpId, appendOpId, dotOpId
  , aValueId, dataEqId
  , anonId, isAnonId

    -- * Predefined qualified identifiers
    -- ** Identifiers for types
  , qArrowId, qUnitId, qBoolId, qCharId, qIntId, qFloatId, qListId, qIOId
  , qSuccessId, isPrimTypeId
    -- ** Identifiers for type classes
  , qEqId, qOrdId, qEnumId, qBoundedId, qReadId, qShowId
  , qNumId, qFractionalId
  , qMonadId, qMonadFailId
  , qDataId
    -- ** Identifiers for constructors
  , qTrueId, qFalseId, qNilId, qConsId, qTupleId, isQTupleId, qTupleArity
    -- ** Identifiers for values
  , qApplyId, qErrorId, qFailedId, qIdId
  , qFromEnumId, qEnumFromId, qEnumFromThenId, qEnumFromToId, qEnumFromThenToId
  , qMaxBoundId, qMinBoundId
  , qLexId, qReadsPrecId, qReadParenId
  , qShowsPrecId, qShowParenId, qShowStringId
  , qAndOpId, qEqOpId, qLeqOpId, qLtOpId, qOrOpId, qAppendOpId, qDotOpId
  , qAValueId, qDataEqId
  , qBindId, qFailId

    -- * Extended functionality
    -- ** Functional patterns
  , fpSelectorId, isFpSelectorId, isQualFpSelectorId
    -- ** Records
  , recSelectorId, qualRecSelectorId, recUpdateId, qualRecUpdateId
  , recordExt, recordExtId, isRecordExtId, fromRecordExtId
  , labelExt, labelExtId, isLabelExtId, fromLabelExtId
  , renameLabel, mkLabelIdent
  ) where

import Control.Monad
import Data.Binary
import Data.Char           (isAlpha, isAlphaNum)
import Data.Function       (on)
import Data.List           (intercalate, isInfixOf, isPrefixOf)
import Data.Maybe          (isJust, fromMaybe)
import GHC.Generics        (Generic)
import Prelude hiding ((<>))

import Curry.Base.Position
import Curry.Base.Span hiding (file)
import Curry.Base.SpanInfo
import Curry.Base.Pretty

-- ---------------------------------------------------------------------------
-- Module identifier
-- ---------------------------------------------------------------------------

-- | Module identifier
data ModuleIdent = ModuleIdent
  { midSpanInfo   :: SpanInfo -- ^ source code 'SpanInfo'
  , midQualifiers :: [String] -- ^ hierarchical idenfiers
  } deriving (Read, Show, Generic, Binary)

instance Eq ModuleIdent where
  (==) = (==) `on` midQualifiers

instance Ord ModuleIdent where
  compare = compare `on` midQualifiers

instance HasSpanInfo ModuleIdent where
  getSpanInfo = midSpanInfo
  setSpanInfo spi a = a { midSpanInfo = spi }
  updateEndPos i =
    setEndPosition (incr (getPosition i) (mIdentLength i - 1)) i

instance HasPosition ModuleIdent where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance Pretty ModuleIdent where
  pPrint = hcat . punctuate dot . map text . midQualifiers

mIdentLength :: ModuleIdent -> Int
mIdentLength a = length (concat (midQualifiers a))
               + length (midQualifiers a)

-- |Construct a 'ModuleIdent' from a list of 'String's forming the
--  the hierarchical module name.
mkMIdent :: [String] -> ModuleIdent
mkMIdent = ModuleIdent NoSpanInfo

-- |Retrieve the hierarchical name of a module
moduleName :: ModuleIdent -> String
moduleName = intercalate "." . midQualifiers

-- |Show the name of an 'ModuleIdent' escaped by ticks
escModuleName :: ModuleIdent -> String
escModuleName m = '`' : moduleName m ++ "'"

-- |Add a source code 'Position' to a 'ModuleIdent'
addPositionModuleIdent :: Position -> ModuleIdent -> ModuleIdent
addPositionModuleIdent = setPosition

-- |Check whether a 'String' is a valid module name.
--
-- Valid module names must satisfy the following conditions:
--
--  * The name must not be empty
--  * The name must consist of one or more single identifiers,
--    seperated by dots
--  * Each single identifier must be non-empty, start with a letter and
--    consist of letter, digits, single quotes or underscores only
isValidModuleName :: String -> Bool
isValidModuleName [] = False -- Module names may not be empty
isValidModuleName qs = all isModuleIdentifier $ splitIdentifiers qs
  where
  -- components of a module identifier may not be null
  isModuleIdentifier []     = False
  -- components of a module identifier must start with a letter and consist
  -- of letter, digits, underscores or single quotes
  isModuleIdentifier (c:cs) = isAlpha c && all isIdent cs
  isIdent c                 = isAlphaNum c || c `elem` "'_"

-- |Resemble the hierarchical module name from a 'String' by splitting
-- the 'String' at inner dots.
--
-- /Note:/ This function does not check the 'String' to be a valid module
-- identifier, use isValidModuleName for this purpose.
fromModuleName :: String -> ModuleIdent
fromModuleName = mkMIdent . splitIdentifiers

-- Auxiliary function to split a hierarchical module identifier at the dots
splitIdentifiers :: String -> [String]
splitIdentifiers s = let (pref, rest) = break (== '.') s in
  pref : case rest of
    []     -> []
    (_:s') -> splitIdentifiers s'

-- ---------------------------------------------------------------------------
-- Simple identifier
-- ---------------------------------------------------------------------------

-- |Simple identifier
data Ident = Ident
  { idSpanInfo :: SpanInfo -- ^ Source code 'SpanInfo'
  , idName     :: String   -- ^ Name of the identifier
  , idUnique   :: Integer  -- ^ Unique number of the identifier
  } deriving (Read, Show, Generic, Binary)

instance Eq Ident where
  Ident _ m i == Ident _ n j = (m, i) == (n, j)

instance Ord Ident where
  Ident _ m i `compare` Ident _ n j = (m, i) `compare` (n, j)

instance HasSpanInfo Ident where
  getSpanInfo = idSpanInfo
  setSpanInfo spi a = a { idSpanInfo = spi }
  updateEndPos i@(Ident (SpanInfo _ [_,ss]) _ _) =
    setEndPosition (end ss) i
  updateEndPos i =
    setEndPosition (incr (getPosition i) (identLength i - 1)) i

instance HasPosition Ident where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance Pretty Ident where
  pPrint (Ident _ x n) | n == globalScope = text x
                       | otherwise        = text x <> dot <> integer n

identLength :: Ident -> Int
identLength a = length (idName a)

-- |Global scope for renaming
globalScope :: Integer
globalScope = 0

-- |Construct an 'Ident' from a 'String'
mkIdent :: String -> Ident
mkIdent x = Ident NoSpanInfo x globalScope

-- |Infinite list of different 'Ident's
identSupply :: [Ident]
identSupply = [ mkNewIdent c i | i <- [0 ..] :: [Integer], c <- ['a'..'z'] ]
  where mkNewIdent c 0 = mkIdent [c]
        mkNewIdent c n = mkIdent $ c : show n

-- |Show function for an 'Ident'
showIdent :: Ident -> String
showIdent (Ident _ x n) | n == globalScope = x
                        | otherwise        = x ++ '.' : show n

-- |Show the name of an 'Ident' escaped by ticks
escName :: Ident -> String
escName i = '`' : idName i ++ "'"

-- |Has the identifier global scope?
hasGlobalScope :: Ident -> Bool
hasGlobalScope = (== globalScope) . idUnique

-- |Is the 'Ident' renamed?
isRenamed :: Ident -> Bool
isRenamed = (/= globalScope) . idUnique

-- |Rename an 'Ident' by changing its unique number
renameIdent :: Ident -> Integer -> Ident
renameIdent ident n = ident { idUnique = n }

-- |Revert the renaming of an 'Ident' by resetting its unique number
unRenameIdent :: Ident -> Ident
unRenameIdent ident = renameIdent ident globalScope

-- |Change the name of an 'Ident' using a renaming function
updIdentName :: (String -> String) -> Ident -> Ident
updIdentName f (Ident p n i) = Ident p (f n) i

-- |Add a 'Position' to an 'Ident'
addPositionIdent :: Position -> Ident -> Ident
addPositionIdent = setPosition

-- |Check whether an 'Ident' identifies an infix operation
isInfixOp :: Ident -> Bool
isInfixOp (Ident _ ('<' : c : cs) _) =
  last (c : cs) /= '>' || not (isAlphaNum c) && c `notElem` "_(["
isInfixOp (Ident _ (c : _) _)    = not (isAlphaNum c) && c `notElem` "_(["
isInfixOp Ident{}                = False -- error "Zero-length identifier"

-- ---------------------------------------------------------------------------
-- Qualified identifier
-- ---------------------------------------------------------------------------

-- |Qualified identifier
data QualIdent = QualIdent
  { qidSpanInfo :: SpanInfo          -- ^ Source code 'SpanInfo'
  , qidModule   :: Maybe ModuleIdent -- ^ optional module identifier
  , qidIdent    :: Ident             -- ^ identifier itself
  } deriving (Read, Show)

instance Eq QualIdent where
  QualIdent _ m i == QualIdent _ n j = (m, i) == (n, j)

instance Ord QualIdent where
  QualIdent _ m i `compare` QualIdent _ n j = (m, i) `compare` (n, j)

instance HasSpanInfo QualIdent where
  getSpanInfo = qidSpanInfo
  setSpanInfo spi a = a { qidSpanInfo = spi }
  updateEndPos i@(QualIdent (SpanInfo _ [_,ss]) _ _) =
    setEndPosition (end ss) i
  updateEndPos i =
    setEndPosition (incr (getPosition i) (qIdentLength i - 1)) i

instance HasPosition QualIdent where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance Pretty QualIdent where
  pPrint = text . qualName

instance Binary QualIdent where
  put (QualIdent sp mid idt) = put sp >> put mid >> put idt
  get = liftM3 QualIdent get get get

qIdentLength :: QualIdent -> Int
qIdentLength (QualIdent _ (Just m) i) = identLength i + mIdentLength m
qIdentLength (QualIdent _ Nothing  i) = identLength i

-- |show function for qualified identifiers)=
qualName :: QualIdent -> String
qualName (QualIdent _ Nothing  x) = idName x
qualName (QualIdent _ (Just m) x) = moduleName m ++ "." ++ idName x

-- |Show the name of an 'QualIdent' escaped by ticks
escQualName :: QualIdent -> String
escQualName qn = '`' : qualName qn ++ "'"

-- |Check whether an 'QualIdent' identifies an infix operation
isQInfixOp :: QualIdent -> Bool
isQInfixOp = isInfixOp . qidIdent

-- ---------------------------------------------------------------------------
-- The functions \texttt{qualify} and \texttt{qualifyWith} convert an
-- unqualified identifier into a qualified identifier (without and with a
-- given module prefix, respectively).
-- ---------------------------------------------------------------------------

-- | Convert an 'Ident' to a 'QualIdent'
qualify :: Ident -> QualIdent
qualify i = QualIdent (fromSrcSpan (getSrcSpan i)) Nothing i

-- | Convert an 'Ident' to a 'QualIdent' with a given 'ModuleIdent'
qualifyWith :: ModuleIdent -> Ident -> QualIdent
qualifyWith mid i = updateEndPos $
  QualIdent (fromSrcSpan (getSrcSpan mid)) (Just mid) i

-- | Convert an 'QualIdent' to a new 'QualIdent' with a given 'ModuleIdent'.
--   If the original 'QualIdent' already contains an 'ModuleIdent' it
--   remains unchanged.
qualQualify :: ModuleIdent -> QualIdent -> QualIdent
qualQualify m (QualIdent _ Nothing x) = qualifyWith m x
qualQualify _ x = x

-- |Qualify an 'Ident' with the 'ModuleIdent' of the given 'QualIdent',
-- if present.
qualifyLike :: QualIdent -> Ident -> QualIdent
qualifyLike (QualIdent _ Nothing  _) x = qualify x
qualifyLike (QualIdent _ (Just m) _) x = qualifyWith m x

-- | Check whether a 'QualIdent' contains a 'ModuleIdent'
isQualified :: QualIdent -> Bool
isQualified = isJust . qidModule

-- | Remove the qualification of an 'QualIdent'
unqualify :: QualIdent -> Ident
unqualify = qidIdent

-- | Remove the qualification with a specific 'ModuleIdent'. If the
--   original 'QualIdent' has no 'ModuleIdent' or a different one, it
--   remains unchanged.
qualUnqualify :: ModuleIdent -> QualIdent -> QualIdent
qualUnqualify _ qid@(QualIdent _   Nothing   _) = qid
qualUnqualify m     (QualIdent spi (Just m') x) = QualIdent spi m'' x
  where m'' | m == m'   = Nothing
            | otherwise = Just m'

-- | Extract the 'Ident' of an 'QualIdent' if it is local to the
--   'ModuleIdent', i.e. if the 'Ident' is either unqualified or qualified
--   with the given 'ModuleIdent'.
localIdent :: ModuleIdent -> QualIdent -> Maybe Ident
localIdent _ (QualIdent _ Nothing   x) = Just x
localIdent m (QualIdent _ (Just m') x)
  | m == m'   = Just x
  | otherwise = Nothing

-- |Check whether the given 'QualIdent' is local to the given 'ModuleIdent'.
isLocalIdent :: ModuleIdent -> QualIdent -> Bool
isLocalIdent mid qid = isJust (localIdent mid qid)

-- | Update a 'QualIdent' by applying functions to its components
updQualIdent :: (ModuleIdent -> ModuleIdent) -> (Ident -> Ident)
             -> QualIdent -> QualIdent
updQualIdent f g (QualIdent spi m x) = QualIdent spi (fmap f m) (g x)

-- ---------------------------------------------------------------------------
-- A few identifiers are predefined here.
-- ---------------------------------------------------------------------------
-- | 'ModuleIdent' for the empty module
emptyMIdent :: ModuleIdent
emptyMIdent = ModuleIdent NoSpanInfo []

-- | 'ModuleIdent' for the main module
mainMIdent :: ModuleIdent
mainMIdent = ModuleIdent NoSpanInfo ["main"]

-- | 'ModuleIdent' for the Prelude
preludeMIdent :: ModuleIdent
preludeMIdent = ModuleIdent NoSpanInfo ["Prelude"]

-- ---------------------------------------------------------------------------
-- Identifiers for types
-- ---------------------------------------------------------------------------

-- | 'Ident' for the type '(->)'
arrowId :: Ident
arrowId = mkIdent "(->)"

-- | 'Ident' for the type/value unit ('()')
unitId :: Ident
unitId = mkIdent "()"

-- | 'Ident' for the type 'Bool'
boolId :: Ident
boolId = mkIdent "Bool"

-- | 'Ident' for the type 'Char'
charId :: Ident
charId = mkIdent "Char"

-- | 'Ident' for the type 'Int'
intId :: Ident
intId = mkIdent "Int"

-- | 'Ident' for the type 'Float'
floatId :: Ident
floatId = mkIdent "Float"

-- | 'Ident' for the type '[]'
listId :: Ident
listId = mkIdent "[]"

-- | 'Ident' for the type 'IO'
ioId :: Ident
ioId = mkIdent "IO"

-- | 'Ident' for the type 'Success'
successId :: Ident
successId = mkIdent "Success"

-- | Construct an 'Ident' for an n-ary tuple where n > 1
tupleId :: Int -> Ident
tupleId n
  | n > 1     = mkIdent $ '(' : replicate (n - 1) ',' ++ ")"
  | otherwise = error $ "Curry.Base.Ident.tupleId: wrong arity " ++ show n

-- | Check whether an 'Ident' is an identifier for an tuple type
isTupleId :: Ident -> Bool
isTupleId (Ident _ x _) = n > 1 && x == idName (tupleId n)
  where n = length x - 1

-- | Compute the arity of a tuple identifier
tupleArity :: Ident -> Int
tupleArity i@(Ident _ x _)
  | n > 1 && x == idName (tupleId n) = n
  | otherwise                        = error $
      "Curry.Base.Ident.tupleArity: no tuple identifier: " ++ showIdent i
  where n = length x - 1

-- ---------------------------------------------------------------------------
-- Identifiers for type classes
-- ---------------------------------------------------------------------------

-- | 'Ident' for the 'Eq' class
eqId :: Ident
eqId = mkIdent "Eq"

-- | 'Ident' for the 'Ord' class
ordId :: Ident
ordId = mkIdent "Ord"

-- | 'Ident' for the 'Enum' class
enumId :: Ident
enumId = mkIdent "Enum"

-- | 'Ident' for the 'Bounded' class
boundedId :: Ident
boundedId = mkIdent "Bounded"

-- | 'Ident' for the 'Read' class
readId :: Ident
readId = mkIdent "Read"

-- | 'Ident' for the 'Show' class
showId :: Ident
showId = mkIdent "Show"

-- | 'Ident' for the 'Num' class
numId :: Ident
numId = mkIdent "Num"

-- | 'Ident' for the 'Fractional' class
fractionalId :: Ident
fractionalId = mkIdent "Fractional"

-- | 'Ident' for the 'Monad' class
monadId :: Ident
monadId = mkIdent "Monad"

-- | 'Ident' for the 'MonadFail' class
monadFailId :: Ident
monadFailId = mkIdent "MonadFail"

-- | 'Ident' for the 'Data' class
dataId :: Ident
dataId = mkIdent "Data"

-- ---------------------------------------------------------------------------
-- Identifiers for constructors
-- ---------------------------------------------------------------------------

-- | 'Ident' for the value 'True'
trueId :: Ident
trueId = mkIdent "True"

-- | 'Ident' for the value 'False'
falseId :: Ident
falseId = mkIdent "False"

-- | 'Ident' for the value '[]'
nilId :: Ident
nilId = mkIdent "[]"

-- | 'Ident' for the function ':'
consId :: Ident
consId = mkIdent ":"

-- ---------------------------------------------------------------------------
-- Identifiers for values
-- ---------------------------------------------------------------------------

-- | 'Ident' for the main function
mainId :: Ident
mainId = mkIdent "main"

-- | 'Ident' for the minus function
minusId :: Ident
minusId = mkIdent "-"

-- | 'Ident' for the minus function for Floats
fminusId :: Ident
fminusId = mkIdent "-."

-- | 'Ident' for the apply function
applyId :: Ident
applyId = mkIdent "apply"

-- | 'Ident' for the error function
errorId :: Ident
errorId = mkIdent "error"

-- | 'Ident' for the failed function
failedId :: Ident
failedId = mkIdent "failed"

-- | 'Ident' for the id function
idId :: Ident
idId = mkIdent "id"

-- | 'Ident' for the maxBound function
maxBoundId :: Ident
maxBoundId = mkIdent "maxBound"

-- | 'Ident' for the minBound function
minBoundId :: Ident
minBoundId = mkIdent "minBound"

-- | 'Ident' for the pred function
predId :: Ident
predId = mkIdent "pred"

-- | 'Ident' for the succ function
succId :: Ident
succId = mkIdent "succ"

-- | 'Ident' for the toEnum function
toEnumId :: Ident
toEnumId = mkIdent "toEnum"

-- | 'Ident' for the fromEnum function
fromEnumId :: Ident
fromEnumId = mkIdent "fromEnum"

-- | 'Ident' for the enumFrom function
enumFromId :: Ident
enumFromId = mkIdent "enumFrom"

-- | 'Ident' for the enumFromThen function
enumFromThenId :: Ident
enumFromThenId = mkIdent "enumFromThen"

-- | 'Ident' for the enumFromTo function
enumFromToId :: Ident
enumFromToId = mkIdent "enumFromTo"

-- | 'Ident' for the enumFromThenTo function
enumFromThenToId :: Ident
enumFromThenToId = mkIdent "enumFromThenTo"

-- | 'Ident' for the lex function
lexId :: Ident
lexId = mkIdent "lex"

-- | 'Ident' for the readsPrec function
readsPrecId :: Ident
readsPrecId = mkIdent "readsPrec"

-- | 'Ident' for the readParen function
readParenId :: Ident
readParenId = mkIdent "readParen"

-- | 'Ident' for the showsPrec function
showsPrecId :: Ident
showsPrecId = mkIdent "showsPrec"

-- | 'Ident' for the showParen function
showParenId :: Ident
showParenId = mkIdent "showParen"

-- | 'Ident' for the showString function
showStringId :: Ident
showStringId = mkIdent "showString"

-- | 'Ident' for the '&&' operator
andOpId :: Ident
andOpId = mkIdent "&&"

-- | 'Ident' for the '==' operator
eqOpId :: Ident
eqOpId = mkIdent "=="

-- | 'Ident' for the '<=' operator
leqOpId :: Ident
leqOpId = mkIdent "<="

-- | 'Ident' for the '<' operator
ltOpId :: Ident
ltOpId = mkIdent "<"

-- | 'Ident' for the '||' operator
orOpId :: Ident
orOpId = mkIdent "||"

-- | 'Ident' for the '++' operator
appendOpId :: Ident
appendOpId = mkIdent "++"

-- | 'Ident' for the '.' operator
dotOpId :: Ident
dotOpId = mkIdent "."

aValueId :: Ident
aValueId = mkIdent "aValue"

dataEqId :: Ident
dataEqId = mkIdent "==="

-- | 'Ident' for anonymous variable
anonId :: Ident
anonId = mkIdent "_"

-- |Check whether an 'Ident' represents an anonymous identifier ('anonId')
isAnonId :: Ident -> Bool
isAnonId = (== anonId) . unRenameIdent

-- ---------------------------------------------------------------------------
-- Qualified Identifiers for types
-- ---------------------------------------------------------------------------

-- | Construct a 'QualIdent' for an 'Ident' using the module prelude
qPreludeIdent :: Ident -> QualIdent
qPreludeIdent = qualifyWith preludeMIdent

-- | 'QualIdent' for the type '(->)'
qArrowId :: QualIdent
qArrowId = qualify arrowId

-- | 'QualIdent' for the type/value unit ('()')
qUnitId :: QualIdent
qUnitId = qualify unitId

-- | 'QualIdent' for the type '[]'
qListId :: QualIdent
qListId = qualify listId

-- | 'QualIdent' for the type 'Bool'
qBoolId :: QualIdent
qBoolId = qPreludeIdent boolId

-- | 'QualIdent' for the type 'Char'
qCharId :: QualIdent
qCharId = qPreludeIdent charId

-- | 'QualIdent' for the type 'Int'
qIntId :: QualIdent
qIntId = qPreludeIdent intId

-- | 'QualIdent' for the type 'Float'
qFloatId :: QualIdent
qFloatId = qPreludeIdent floatId

-- | 'QualIdent' for the type 'IO'
qIOId :: QualIdent
qIOId = qPreludeIdent ioId

-- | 'QualIdent' for the type 'Success'
qSuccessId :: QualIdent
qSuccessId = qPreludeIdent successId

-- | Check whether an 'QualIdent' is an primary type constructor
isPrimTypeId :: QualIdent -> Bool
isPrimTypeId tc = tc `elem` [qArrowId, qUnitId, qListId] || isQTupleId tc

-- ---------------------------------------------------------------------------
-- Qualified Identifiers for type classes
-- ---------------------------------------------------------------------------

-- | 'QualIdent' for the 'Eq' class
qEqId :: QualIdent
qEqId = qPreludeIdent eqId

-- | 'QualIdent' for the 'Ord' class
qOrdId :: QualIdent
qOrdId = qPreludeIdent ordId

-- | 'QualIdent' for the 'Enum' class
qEnumId :: QualIdent
qEnumId = qPreludeIdent enumId

-- | 'QualIdent' for the 'Bounded' class
qBoundedId :: QualIdent
qBoundedId = qPreludeIdent boundedId

-- | 'QualIdent' for the 'Read' class
qReadId :: QualIdent
qReadId = qPreludeIdent readId

-- | 'QualIdent' for the 'Show' class
qShowId :: QualIdent
qShowId = qPreludeIdent showId

-- | 'QualIdent' for the 'Num' class
qNumId :: QualIdent
qNumId = qPreludeIdent numId

-- | 'QualIdent' for the 'Fractional' class
qFractionalId :: QualIdent
qFractionalId = qPreludeIdent fractionalId

-- | 'QualIdent' for the 'Monad' class
qMonadId :: QualIdent
qMonadId = qPreludeIdent monadId

-- | 'QualIdent' for the 'MonadFail' class
qMonadFailId :: QualIdent
qMonadFailId = qPreludeIdent monadFailId

-- | 'QualIdent' for the 'Data' class
qDataId :: QualIdent
qDataId = qPreludeIdent dataId

-- ---------------------------------------------------------------------------
-- Qualified Identifiers for constructors
-- ---------------------------------------------------------------------------

-- | 'QualIdent' for the constructor 'True'
qTrueId :: QualIdent
qTrueId = qPreludeIdent trueId

-- | 'QualIdent' for the constructor 'False'
qFalseId :: QualIdent
qFalseId = qPreludeIdent falseId

-- | 'QualIdent' for the constructor '[]'
qNilId :: QualIdent
qNilId = qualify nilId

-- | 'QualIdent' for the constructor ':'
qConsId :: QualIdent
qConsId = qualify consId

-- | 'QualIdent' for the type of n-ary tuples
qTupleId :: Int -> QualIdent
qTupleId = qualify . tupleId

-- | Check whether an 'QualIdent' is an identifier for an tuple type
isQTupleId :: QualIdent -> Bool
isQTupleId = isTupleId . unqualify

-- | Compute the arity of an qualified tuple identifier
qTupleArity :: QualIdent -> Int
qTupleArity = tupleArity . unqualify

-- ---------------------------------------------------------------------------
-- Qualified Identifiers for values
-- ---------------------------------------------------------------------------

-- | 'QualIdent' for the apply function
qApplyId :: QualIdent
qApplyId = qPreludeIdent applyId

-- | 'QualIdent' for the error function
qErrorId :: QualIdent
qErrorId = qPreludeIdent errorId

-- | 'QualIdent' for the failed function
qFailedId :: QualIdent
qFailedId = qPreludeIdent failedId

-- | 'QualIdent' for the id function
qIdId :: QualIdent
qIdId = qPreludeIdent idId

-- | 'QualIdent' for the maxBound function
qMaxBoundId :: QualIdent
qMaxBoundId = qPreludeIdent maxBoundId

-- | 'QualIdent' for the minBound function
qMinBoundId :: QualIdent
qMinBoundId = qPreludeIdent minBoundId

-- | 'QualIdent' for the fromEnum function
qFromEnumId :: QualIdent
qFromEnumId = qPreludeIdent fromEnumId

-- | 'QualIdent' for the enumFrom function
qEnumFromId :: QualIdent
qEnumFromId = qPreludeIdent enumFromId

-- | 'QualIdent' for the enumFromThen function
qEnumFromThenId :: QualIdent
qEnumFromThenId = qPreludeIdent enumFromThenId

-- | 'QualIdent' for the enumFromTo function
qEnumFromToId :: QualIdent
qEnumFromToId = qPreludeIdent enumFromToId

-- | 'QualIdent' for the enumFromThenTo function
qEnumFromThenToId :: QualIdent
qEnumFromThenToId = qPreludeIdent enumFromThenToId

-- | 'QualIdent' for the lex function
qLexId :: QualIdent
qLexId = qPreludeIdent lexId

-- | 'QualIdent' for the readsPrec function
qReadsPrecId :: QualIdent
qReadsPrecId = qPreludeIdent readsPrecId

-- | 'QualIdent' for the readParen function
qReadParenId :: QualIdent
qReadParenId = qPreludeIdent readParenId

-- | 'QualIdent' for the showsPrec function
qShowsPrecId :: QualIdent
qShowsPrecId = qPreludeIdent showsPrecId

-- | 'QualIdent' for the showParen function
qShowParenId :: QualIdent
qShowParenId = qPreludeIdent showParenId

-- | 'QualIdent' for the showString function
qShowStringId :: QualIdent
qShowStringId = qPreludeIdent showStringId

-- | 'QualIdent' for the '&&' operator
qAndOpId :: QualIdent
qAndOpId = qPreludeIdent andOpId

-- | 'QualIdent' for the '==' operator
qEqOpId :: QualIdent
qEqOpId = qPreludeIdent eqOpId

-- | 'QualIdent' for the '<=' operator
qLeqOpId :: QualIdent
qLeqOpId = qPreludeIdent leqOpId

-- | 'QualIdent' for the '<' operator
qLtOpId :: QualIdent
qLtOpId = qPreludeIdent ltOpId

-- | 'QualIdent' for the '||' operator
qOrOpId :: QualIdent
qOrOpId = qPreludeIdent orOpId

-- | 'QualIdent' for the '.' operator
qDotOpId :: QualIdent
qDotOpId = qPreludeIdent dotOpId

qAValueId :: QualIdent
qAValueId = qPreludeIdent aValueId

qDataEqId :: QualIdent
qDataEqId = qPreludeIdent dataEqId

-- | 'QualIdent' for the '++' operator
qAppendOpId :: QualIdent
qAppendOpId = qPreludeIdent appendOpId

-- | 'QualIdent' for the '>>=' operator
qBindId :: QualIdent
qBindId = qPreludeIdent $ mkIdent ">>="

-- | 'QualIdent' for the 'fail' method from the 'MonadFail' class
qFailId :: QualIdent
qFailId = qPreludeIdent $ mkIdent "fail"

-- ---------------------------------------------------------------------------
-- Micellaneous functions for generating and testing extended identifiers
-- ---------------------------------------------------------------------------

-- Functional patterns

-- | Annotation for function pattern identifiers
fpSelExt :: String
fpSelExt = "_#selFP"

-- | Construct an 'Ident' for a functional pattern
fpSelectorId :: Int -> Ident
fpSelectorId n = mkIdent $ fpSelExt ++ show n

-- | Check whether an 'Ident' is an identifier for a functional pattern
isFpSelectorId :: Ident -> Bool
isFpSelectorId = (fpSelExt `isInfixOf`) . idName

-- | Check whether an 'QualIdent' is an identifier for a function pattern
isQualFpSelectorId :: QualIdent -> Bool
isQualFpSelectorId = isFpSelectorId . unqualify

-- Record selection

-- | Annotation for record selection identifiers
recSelExt :: String
recSelExt = "_#selR@"

-- | Construct an 'Ident' for a record selection pattern
recSelectorId :: QualIdent -- ^ identifier of the record
              -> Ident     -- ^ identifier of the label
              -> Ident
recSelectorId = mkRecordId recSelExt

-- | Construct a 'QualIdent' for a record selection pattern
qualRecSelectorId :: ModuleIdent -- ^ default module
                  -> QualIdent   -- ^ record identifier
                  -> Ident       -- ^ label identifier
                  -> QualIdent
qualRecSelectorId m r l = qualRecordId m r $ recSelectorId r l

-- Record update

-- | Annotation for record update identifiers
recUpdExt :: String
recUpdExt = "_#updR@"

-- | Construct an 'Ident' for a record update pattern
recUpdateId :: QualIdent -- ^ record identifier
            -> Ident     -- ^ label identifier
            -> Ident
recUpdateId = mkRecordId recUpdExt

-- | Construct a 'QualIdent' for a record update pattern
qualRecUpdateId :: ModuleIdent -- ^ default module
                -> QualIdent   -- ^ record identifier
                -> Ident       -- ^ label identifier
                -> QualIdent
qualRecUpdateId m r l = qualRecordId m r $ recUpdateId r l

-- Auxiliary function to construct a selector/update identifier
mkRecordId :: String -> QualIdent -> Ident -> Ident
mkRecordId ann r l = mkIdent $ concat
  [ann, idName (unqualify r), ".", idName l]

-- Auxiliary function to qualify a selector/update identifier
qualRecordId :: ModuleIdent -> QualIdent -> Ident -> QualIdent
qualRecordId m r = qualifyWith (fromMaybe m $ qidModule r)

-- Record tyes

-- | Annotation for record identifiers
recordExt :: String
recordExt = "_#Rec:"

-- | Construct an 'Ident' for a record
recordExtId :: Ident -> Ident
recordExtId r = mkIdent $ recordExt ++ idName r

-- | Check whether an 'Ident' is an identifier for a record
isRecordExtId :: Ident -> Bool
isRecordExtId = (recordExt `isPrefixOf`) . idName

-- | Retrieve the 'Ident' from a record identifier
fromRecordExtId :: Ident -> Ident
fromRecordExtId r
  | p == recordExt = mkIdent r'
  | otherwise      = r
 where (p, r') = splitAt (length recordExt) (idName r)

-- Record labels

-- | Annotation for record label identifiers
labelExt :: String
labelExt = "_#Lab:"

-- | Construct an 'Ident' for a record label
labelExtId :: Ident -> Ident
labelExtId l = mkIdent $ labelExt ++ idName l

-- | Check whether an 'Ident' is an identifier for a record label
isLabelExtId :: Ident -> Bool
isLabelExtId = (labelExt `isPrefixOf`) . idName

-- | Retrieve the 'Ident' from a record label identifier
fromLabelExtId :: Ident -> Ident
fromLabelExtId l
  | p == labelExt = mkIdent l'
  | otherwise     = l
 where (p, l') = splitAt (length labelExt) (idName l)

-- | Construct an 'Ident' for a record label
mkLabelIdent :: String -> Ident
mkLabelIdent c = renameIdent (mkIdent c) (-1)

-- | Rename an 'Ident' for a record label
renameLabel :: Ident -> Ident
renameLabel l = renameIdent l (-1)
