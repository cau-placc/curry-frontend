{- |
    Module      :  $Header$
    Description :  Monads for message handling
    Copyright   :  2009        Holger Siegel
                   2012 - 2015 Björn Peemöller
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The type message represents a compiler message with an optional source
    code position.
-}
module Curry.Base.Message
  ( Message (..), message, posMessage, spanMessage, spanInfoMessage, withFixes
  , showWarning, showError
  , ppMessage, ppWarning, ppError, ppMessages, ppMessagesWithPreviews
  ) where

import Prelude hiding ((<>))
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Base.QuickFix (QuickFix (..))
import Curry.Base.Span
import Curry.Base.SpanInfo

-- ---------------------------------------------------------------------------
-- Message
-- ---------------------------------------------------------------------------

-- |Compiler message
data Message = Message
  { msgSpanInfo :: SpanInfo   -- ^ span in the source code
  , msgTxt      :: Doc        -- ^ the message itself
  , msgFixes    :: [QuickFix] -- ^ fixes that resolve the issue
  }

instance Eq Message where
  Message s1 t1 fs1 == Message s2 t2 fs2 = (s1, show t1, fs1) == (s2, show t2, fs2)

instance Ord Message where
  Message s1 t1 fs1 `compare` Message s2 t2 fs2 = compare (s1, show t1, fs1) (s2, show t2, fs2)

instance Show Message where
  showsPrec _ = shows . ppMessage

instance HasPosition Message where
  getPosition = getStartPosition
  setPosition = setStartPosition

instance HasSpanInfo Message where
  getSpanInfo       = msgSpanInfo
  setSpanInfo spi m = m { msgSpanInfo = spi }

instance Pretty Message where
  pPrint = ppMessage

-- |Construct a 'Message' without a 'SpanInfo'
message :: Doc -> Message
message msg = Message NoSpanInfo msg []

-- |Construct a message from a position.
posMessage :: HasPosition p => p -> Doc -> Message
posMessage p = spanMessage $ pos2Span $ getPosition p

-- |Construct a message from a span and a text
spanMessage :: Span -> Doc -> Message
spanMessage s = spanInfoMessage $ fromSrcSpan s

-- |Construct a message from an entity with a 'SpanInfo' and a text
spanInfoMessage :: HasSpanInfo s => s -> Doc -> Message
spanInfoMessage s msg = Message (getSpanInfo s) msg []

-- |Adds the given fixes to the message.
withFixes :: [QuickFix] -> Message -> Message
withFixes fs m = m { msgFixes = msgFixes m ++ fs }

-- |Show a 'Message' as a warning
showWarning :: Message -> String
showWarning = show . ppWarning

-- |Show a 'Message' as an error
showError :: Message -> String
showError = show . ppError

-- |Pretty print a 'Message'
ppMessage :: Message -> Doc
ppMessage = ppAs ""

-- |Pretty print a 'Message' as a warning
ppWarning :: Message -> Doc
ppWarning = ppAs "Warning"

-- |Pretty print a 'Message' as an error
ppError :: Message -> Doc
ppError = ppAs "Error"

-- |Pretty print a 'Message' with a given key
ppAs :: String -> Message -> Doc
ppAs key (Message mbSpanInfo txt _) = hsep (filter (not . isEmpty) [spanPP, keyPP]) $$ nest 4 txt
  where
  spanPP = ppCompactSpan $ getSrcSpan mbSpanInfo
  keyPP = if null key then empty else text key <> colon

-- |Pretty print a list of 'Message's by vertical concatenation
ppMessages :: (Message -> Doc) -> [Message] -> Doc
ppMessages ppFun = foldr ((\m ms -> text "" $+$ m $+$ ms) . ppFun) empty

-- |Pretty print a list of 'Message's with previews by vertical concatenation
ppMessagesWithPreviews :: (Message -> Doc) -> [Message] -> IO Doc
ppMessagesWithPreviews ppFun = fmap (foldr (\m ms -> text "" $+$ m $+$ ms) empty) . mapM ppFunWithPreview
  where ppFunWithPreview m = do preview <- case m of
                                  Message (SpanInfo sp _) _ _ -> ppSpanPreview sp
                                  _                           -> return empty
                                return $ ppFun m $+$ preview
