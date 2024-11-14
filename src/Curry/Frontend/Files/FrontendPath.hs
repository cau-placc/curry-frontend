{- |
    Module      :  $Header$
    Description :  File pathes
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains functions to obtain the version number and path
    of the front end binary.
-}
module Files.FrontendPath (getFrontend, frontendGreeting, frontendVersion) where

import Data.Version (showVersion)
import System.FilePath ((</>))
import Paths_curry_frontend

-- | Show a greeting of the current front end
frontendGreeting :: String
frontendGreeting = "This is the Curry front end, version " ++ frontendVersion

-- | Retrieve the version number of frontend
frontendVersion :: String
frontendVersion = showVersion version

-- | Retrieve the location of the front end executable
getFrontend :: IO String
getFrontend = do
  frontendDir <- getBinDir
  return $ frontendDir </> "curry-frontend"
