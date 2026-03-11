-- |
-- Copyright   : (c) 2023 - Thiebaux Valentin
-- License     : GPL v3 (see LICENSE)
--
--
-- Parsing macros
------------------------------------------------------------------------------

module Theory.Text.Parser.Macro (
    macros
    , getMacroName
)
where

import           Prelude                    hiding (id)
import qualified Data.ByteString.Char8      as BC
import qualified Data.Set                   as S
import           Data.List

import           Control.Monad
import           Text.Parsec                hiding ((<|>))

import           Term.Macro

import           Theory
import           Theory.Text.Parser.Token
import           Theory.Text.Parser.Term

macros :: Parser [LNMacro]
macros = do
    mcs <- symbol "macros" *> colon *> commaSep macro
    return mcs
    where
      macro = do
        op <- BC.pack <$> identifier
        when (BC.unpack op `elem` reservedBuiltins)
            $ error $ "`" ++ show op ++ "` is a reserved function name for builtins."
        args <- parens $ commaSep lvar
        unless (length args == length (nub args))
            $ error $ show op ++ " have two arguments with the same name."
        out <- equalSign *> msetterm False llit
        sign <- sig <$> getState
        let mc = (op, args, out)
        let k = length args
        case lookup op (S.toList $ stFunSyms sign) of
            Just _ -> fail $ "Conflicting name for macro " ++ BC.unpack op
            _ -> do
                modifyStateSig $ addMacroSym (op,(k,Private,Destructor))
                return mc

getMacroName :: LNMacro -> String
getMacroName (op, _, _) = BC.unpack op