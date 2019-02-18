{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Theories with Processes to mrs


module Sapic (
    translate
) where
import Text.ParserCombinators.Parsec
import Theory.Text.Parser
import Theory
translate x = x


-- translate :: Either ParseError OpenTheory -> Either ParseError OpenTheory
-- translate x = parseOpenTheoryString ["lol","fail"] "fail"
