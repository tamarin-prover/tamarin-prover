module Utils.ApplicativeParsec (
  module Control.Applicative,
  module Text.ParserCombinators.Parsec,
  commaWS,
  pNat,
  eol
) where

import Control.Applicative hiding (Const )
-- Hide a few names that are provided by Applicative.
import Text.ParserCombinators.Parsec hiding (many, optional, (<|>))

pNat :: GenParser Char st Int
pNat = read <$> many1 digit

commaWS :: GenParser Char st ()
commaWS = char ',' *> spaces

eol :: GenParser Char st ()
eol = char '\n' *> return ()
