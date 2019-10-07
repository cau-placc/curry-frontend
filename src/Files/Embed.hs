{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE OverloadedStrings #-}
module Files.Embed (embedDataFile, cssFileName) where

import Prelude                    (FilePath, Monad(..), ($), fromIntegral)
import Data.ByteString.Unsafe     (unsafePackAddressLen)
import Data.ByteString            (ByteString, unpack, length, readFile)
import System.IO.Unsafe           (unsafePerformIO)
import Language.Haskell.TH.Syntax (Q, Exp(..), Lit(..), runIO)
import Paths_curry_frontend       (getDataFileName)

-- | embed a file from the data dir within the code
embedDataFile :: FilePath -> Q Exp
embedDataFile fn = do
  fp <- runIO $ getDataFileName fn
  c <- runIO $ readFile fp
  bsToExp c

bsToExp :: ByteString -> Q Exp
bsToExp bs =
  return $ VarE 'unsafePerformIO
    `AppE` (VarE 'unsafePackAddressLen
    `AppE` LitE (IntegerL $ fromIntegral $ length bs)
    `AppE` LitE (StringPrimL $ unpack bs))

cssFileName :: FilePath
cssFileName = "currysource.css"
