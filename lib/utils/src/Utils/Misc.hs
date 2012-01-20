{-# LANGUAGE DeriveDataTypeable, RankNTypes, ScopedTypeVariables, BangPatterns #-}
module Utils.Misc (
    invertMap

  , pNat
  , commaWS

  -- * Environment
  , envIsSet
  , getEnvMaybe

  -- * List operations
  , subsetOf
  , noDuplicates
  , equivClasses  
 
  -- * Control
  , whileTrue

  -- * Hashing
  , stringSHA256
) where

import Data.List
import System.Environment
import System.IO.Unsafe
import Data.Maybe
import qualified Data.Set as S
import Data.Map ( Map )
import qualified Data.Map as M
import Control.Applicative

import Text.ParserCombinators.Parsec hiding (many, optional, (<|>))

import Data.Digest.Pure.SHA      (bytestringDigest, sha256)
import Blaze.ByteString.Builder  (toLazyByteString)
import qualified Data.ByteString.Char8              as C8
import qualified Data.ByteString.Lazy               as L
import qualified Data.ByteString.Base64             as B64  (encode)
import qualified Blaze.ByteString.Builder.Char.Utf8 as Utf8 (fromString)

-- | @noDuplicates xs@ returns @True@ if the list @xs@ contains no duplicates
noDuplicates :: (Ord a) => [a] -> Bool
noDuplicates xs = all ((==1).length) . group . sort $ xs

-- | @getEnvMaybe k@ returns @Just v@ if @k=v@ is in the environment and @Nothing@ otherwise
getEnvMaybe :: String -> Maybe String
getEnvMaybe k = unsafePerformIO $ do
  l <- getEnvironment
  return $ lookup k l

-- | @envIsSet k@ returns @True@ if there is a v such @k=v@ is in the environment and @False@ otherwise.
envIsSet :: String -> Bool
envIsSet k = isJust $ getEnvMaybe k

-- | @subsetOf xs ys@ return @True@ if @set xs@ is a subset of @set ys@ 
subsetOf :: Ord a => [a] -> [a] -> Bool
subsetOf xs ys = (S.fromList xs) `S.isSubsetOf` (S.fromList ys)

-- | Inverts a bijective Map.
invertMap :: (Ord k, Ord v) => Map k v -> Map v k
invertMap = M.fromList . map (uncurry (flip (,))) . M.toList

-- | parse natural number
pNat :: GenParser Char st Int
pNat = read <$> many1 digit

-- | parse comma
commaWS :: GenParser Char st ()
commaWS = char ',' *> spaces

-- | @whileTrue m@ iterates m until it returns @False@.
--   Returns the number of iterations @m@ was run. @0@
--   means @m@ never returned @True@.
whileTrue :: Monad m => m Bool -> m Int
whileTrue m = go 0
  where go (!n) = m >>= \b -> if b then go (n+1) else return n

-- | Compute the equality classes given wrto a partial function.
equivClasses :: (Ord a, Ord b) => [(a, b)] -> M.Map b (S.Set a)
equivClasses = 
    foldl' insertEdge M.empty 
  where
    insertEdge m (from,to) = M.insertWith' S.union to (S.singleton from) m

-- | The SHA-256 hash of a string in base64 notation.
stringSHA256 :: String -> String
stringSHA256 =
    C8.unpack . urlEncodeBase64 . C8.concat . L.toChunks
  . bytestringDigest . sha256 . toLazyByteString . Utf8.fromString
  where
   urlEncodeBase64 = C8.init . C8.map replace . B64.encode
   replace '/' = '_'
   replace '+' = '-'
   replace c   = c