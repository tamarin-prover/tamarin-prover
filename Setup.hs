import Distribution.Simple
main = defaultMain

{- Inferring the package version from git. Posted by https://github.com/hvr
 -
 - https://gist.github.com/656738

import Control.Exception
import Control.Monad
import Data.Maybe
import Data.Version
import Distribution.PackageDescription (PackageDescription(..), HookedBuildInfo, GenericPackageDescription(..))
import Distribution.Package (PackageIdentifier(..))
import Distribution.Simple (defaultMainWithHooks, simpleUserHooks, UserHooks(..))
import Distribution.Simple.LocalBuildInfo (LocalBuildInfo(..))
import Distribution.Simple.Setup (BuildFlags(..), ConfigFlags(..))
import Distribution.Simple.Utils (die)
import System.Process (readProcess)
import Text.ParserCombinators.ReadP (readP_to_S)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks
         { confHook = myConfHook
         , buildHook = myBuildHook
         }

-- configure hook
myConfHook :: (GenericPackageDescription, HookedBuildInfo)
           -> ConfigFlags
           -> IO LocalBuildInfo
myConfHook (gpdesc, hbinfo) cfg = do
  let GenericPackageDescription {
        packageDescription = pdesc@PackageDescription {
           package = pkgIden }} = gpdesc

  gitVersion <- inferVersionFromGit (pkgVersion (package pdesc))

  let gpdesc' = gpdesc {
        packageDescription = pdesc {
           package = pkgIden { pkgVersion = gitVersion } } }

  -- putStrLn $ showVersion gitVersion

  confHook simpleUserHooks (gpdesc', hbinfo) cfg


-- build hook
myBuildHook :: PackageDescription
            -> LocalBuildInfo
            -> UserHooks
            -> BuildFlags
            -> IO ()
myBuildHook pdesc lbinfo uhooks bflags = do
  let lastVersion = pkgVersion $ package pdesc

  gitVersion <- inferVersionFromGit lastVersion 

  when (gitVersion /= lastVersion) $
    die("The version reported by git '" ++ showVersion gitVersion ++
        "' has changed since last time this package was configured (version was '" ++
        showVersion lastVersion ++ "' back then), please re-configure package")

  buildHook simpleUserHooks pdesc lbinfo uhooks bflags

-- |Infer package version from Git tags. Uses `git describe` to infer 'Version'.
inferVersionFromGit :: Version -> IO Version
inferVersionFromGit version0 = do
  ver_line <- init `liftM` readProcess "git"
              [ "describe"
              , "--abbrev=5"
              , "--tags"
              , "--match=v[0-9].[0-9][0-9]"
              , "--dirty"
              , "--long"
              , "--always"
              ] ""

  -- ver_line <- return "v0.1-42-gf9f4eb3-dirty"
  putStrLn ver_line
  -- let versionStr = ver_line -- (head ver_line == 'v') `assert` replaceFirst '-' '.' (tail ver_line)
      -- Just version = listToMaybe [ p | (p, "") <- readP_to_S parseVersion versionStr ]

  return version0

{-
-- | Helper for replacing first occurrence of character by another one.
replaceFirst :: Eq a => a -> a -> [a] -> [a]
replaceFirst _ _ [] = []
replaceFirst o r (x:xs) | o == x    = r : xs
                        | otherwise = x : replaceFirst o r xs
-}

-}
