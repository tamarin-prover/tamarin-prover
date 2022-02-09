-- |
-- Copyright   : (c)  2019-2021: Robert Künnemann, Johannes Wocker, Kevin Morio, Charlie Jacomme
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : portable
--
-- Parsing SAPIC processes. See the MANUAL for a high-level description of
-- the syntax.

module Theory.Text.Parser.Sapic(
    process
    , processDef
)
where

import           Prelude                    hiding (id, (.))
import qualified Data.ByteString.Char8      as BC
import           Data.Label
-- import           Data.Monoid                hiding (Last)
import           Control.Applicative        hiding (empty, many, optional)
import qualified Control.Monad.Catch        as Catch
import           Text.Parsec                hiding ((<|>))
import           Theory
import           Theory.Sapic
import           Theory.Text.Parser.Token

import           Theory.Text.Parser.Term
import           Theory.Text.Parser.Fact
import           Theory.Text.Parser.Rule
import Theory.Text.Parser.Let
import Theory.Text.Parser.Formula


-- used for debugging
-- println :: String -> ParsecT String u Identity ()
-- println str = traceShowM str

-- parse a process definition (let block)
processDef :: OpenTheory -> Parser ProcessDef
processDef thy= do
                letIdentifier
                i <- BC.pack <$> identifier
                equalSign
                p <- process thy
                return (ProcessDef (BC.unpack i) p )

-- | Parse a single sapic action, i.e., a thing that can appear before the ";"
-- (This includes almost all items that are followed by one instead of two
-- processes, the exception is replication)
sapicAction :: Parser SapicAction
sapicAction = try (do
                        _ <- symbol "new"
                        s <- msgvar
                        return (New s)
                   )
               <|> try (do
                        _ <- symbol "in"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- symbol ")"
                        return (ChIn Nothing t)
                   )
               <|> try (do
                        _ <- symbol "in"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- comma
                        t' <- msetterm False llit
                        _ <- symbol ")"
                        return (ChIn (Just t) t')
                   )
               <|> try (do
                        _ <- symbol "out"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- symbol ")"
                        return (ChOut Nothing t)
                   )
               <|> try (do
                        _ <- symbol "out"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- comma
                        t' <- msetterm False llit
                        _ <- symbol ")"
                        return (ChOut (Just t) t')
                   )
               <|> try (do
                        _ <- symbol "insert"
                        t <- msetterm False llit
                        _ <- comma
                        t' <- msetterm False llit
                        return (Insert t t')
                   )
               <|> try (do
                        _ <- symbol "delete"
                        t <- msetterm False llit
                        return (Delete t)
                   )
               <|> try (do
                        _ <- symbol "lock"
                        t <- msetterm False llit
                        return (Lock t)
                   )
               <|> try (do
                        _ <- symbol "unlock"
                        t <- msetterm False llit
                        return (Unlock t)
                   )
               <|> try (do
                        _ <- symbol "event"
                        f <- fact llit
                        return (Event f)
                   )
               <|> try ( MSR <$> genericRule)

-- | Parse a process. Process combinators like | are left-associative (not that
-- it matters), so we had to split the grammar for processes in two, so that
-- the precedence is expressed in a way that can be directly encoded in Parsec.
-- This is the grammar, more or less. (Process definition is written down in
-- a way that you can read of the precise definition from there
-- process:
--     | LP process RP
--     | LP process RP AT multterm
--     | actionprocess PARALLEL process
--     | actionprocess PLUS process
--     null

-- actionprocess:
--     | sapic_action optprocess
--     | NULL
--     | REP process
--     | IF if_cond THEN process ELSE process
--     | IF if_cond THEN process
--     | LOOKUP term AS literal IN process ELSE process
--     | LOOKUP term AS literal IN process
--     | LET id_eq_termseq IN process
--     | LET id_not_res EQ REPORT LP multterm RP IN process
--     | IDENTIFIER
--     | msr
process :: OpenTheory -> Parser Process
process thy=
            -- left-associative NDC and parallel using chainl1.
            -- Note: this roughly encodes the following grammar:
            -- <|>   try   (do
            --             p1 <- actionprocess thy
            --             opParallel
            --             p2 <- process thy
            --             return (ProcessParallel p1 p2))
                  try  (chainl1 (actionprocess thy) (
                             do { _ <- try opNDC; return (ProcessComb NDC mempty)}
                         <|> do { _ <- try opParallelDepr; return (ProcessComb Parallel mempty)}
                         <|> do { _ <- opParallel; return (ProcessComb Parallel mempty)}
                  ))
            <|>   try (do    -- parens parser + at multterm
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        _ <- symbol "@"
                        m <- msetterm False llit
                        return $ paddAnn p [ProcessLoc m]
                        )
                        -- TODO SAPIC parser: multterm return
                        -- This is what SAPIC did:  | LP process RP AT multterm                      { substitute "_loc_" $5 $2 }
            <|>    try  (do -- parens parser
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        return p)
            <|>    try  (do -- let expression parser
                        subst <- letBlock
                        p <- process thy
                        case Catch.catch (applyProcess subst p) (\ e  -> error $ prettyLetExceptions e) of
                            (Left err) -> fail $ show err -- Should never occur, we handle everything above
                            (Right p') -> return p'
                        )
            <|>    do       -- action at top-level
                        p <- actionprocess thy
                        return p

actionprocess :: OpenTheory -> Parser Process
actionprocess thy=
            try (do         -- replication parser
                        _ <- symbol "!"
                        p <- process thy
                        return (ProcessAction Rep mempty p))
            <|> try (do     -- lookup / if with and w/o else branches
                        _ <- symbol "lookup"
                        t <- msetterm False llit
                        _ <- symbol "as"
                        v <- msgvar
                        _ <- symbol "in"
                        p <- process thy
                        _ <- symbol "else"
                        q <- process thy
                        return (ProcessComb (Lookup t v) mempty p q)
                   )
            <|> try (do
                        _ <- symbol "lookup"
                        t <- msetterm False llit
                        _ <- symbol "as"
                        v <- msgvar
                        _ <- symbol "in"
                        p <- process thy
                        return (ProcessComb (Lookup t v) mempty p (ProcessNull mempty))
                   )
            <|> try (do
                        _ <- symbol "if"
                        t1 <- msetterm False llit
                        _ <- opEqual
                        t2 <- msetterm False llit
                        _ <- symbol "then"
                        p <- process thy
                        q <- option (ProcessNull mempty) (symbol "else" *> process thy)
                        return (ProcessComb (CondEq t1 t2  ) mempty p q)
                        <?> "conditional process (with equality)"
                   )
            <|> try (do
                        _ <- symbol "if"
                        frml <- standardFormula
                        _ <- symbol "then"
                        p <- process thy
                        q <- option (ProcessNull mempty) (symbol "else" *> process thy)
                        return (ProcessComb (Cond frml) mempty p q)
                        <?> "conditional process (with predicate)"
                   )
            -- <|> try (do
            --             _ <- symbol "if"
            --             t1 <- msetterm llit
            --             _ <- opEqual
            --             t2 <- msetterm llit
            --             _ <- symbol "then"
            --             p <- process thy
            --             return (ProcessComb (CondEq t1 t2  ) mempty p (ProcessNull mempty))
            --        )
            -- <|> try (do
            --             _ <- symbol "if"
            --             pr <- fact llit
            --             _ <- symbol "then"
            --             p <- process thy
            --             return (ProcessComb (Cond pr) mempty p (ProcessNull mempty))
            --        )
            <|> try ( do  -- sapic actions are constructs separated by ";"
                        s <- sapicAction
                        _ <- opSeq
                        p <- actionprocess thy
                        return (ProcessAction s mempty p))
            <|> try ( do  -- allow trailing actions (syntactic sugar for action; 0)
                        s <- sapicAction
                        return (ProcessAction s mempty (ProcessNull mempty)))
            <|> try (do   -- null process: terminating element
                        _ <- opNull
                        return (ProcessNull mempty) )
            <|> try   (do -- parse identifier
                        -- println ("test process identifier parsing Start")
                        i <- BC.pack <$> identifier
                        a <- let p = checkProcess (BC.unpack i) thy in
                             (\x -> paddAnn x [ProcessName $ BC.unpack i]) <$> p
                        return a
                        )
            <|>    try  (do -- let expression parser
                        subst <- letBlock
                        p     <- process thy
                        case Catch.catch (applyProcess subst p) (\ e  -> error $ prettyLetExceptions e) of
                            (Left err) -> fail $ show err -- Should never occur, we handle everything above
                            (Right p') -> return p'
                        )
            <|>   try (do    -- parens parser + at multterm
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        _ <- symbol "@"
                        m <- msetterm False llit
                        return $ paddAnn p [ProcessLoc m]
                        )
            <|> try (do        -- parens parser
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        return p
                    )

-- | checks if process exists, if not -> error
checkProcess :: String -> OpenTheory -> Parser Process
checkProcess i thy = case lookupProcessDef i thy of
    Just p -> return $ get pBody p
    Nothing -> fail $ "process not defined: " ++ i
