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
<<<<<<< HEAD
import Text.ParserCombinators.Parsec
import Theory.Text.Parser
import Theory
translate x = x


-- translate :: Either ParseError OpenTheory -> Either ParseError OpenTheory
-- translate x = parseOpenTheoryString ["lol","fail"] "fail"
=======

translate (Left x) = x
translate (Right th) = 
    fold_left (addProtoRule th) th []
    where
        process = theoryProcesses th
        msrs =  []
-- translate x = Left (Parsec.ParseError "Lol")
>>>>>>> d51d092d5f8d1ba2f34bd6156a2f23b5a66de67e
