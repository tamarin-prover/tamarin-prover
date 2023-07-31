-- |
-- Copyright   : (c)  2019-2021: Robert Künnemann, Johannes Wocker, Kevin Morio, Charlie Jacomme
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : portable
--
-- Parsing SAPIC processes. See the MANUAL for a high-level description of
-- the syntax.

{-# LANGUAGE TupleSections #-}
module Theory.Text.Parser.Sapic(
    process
    , processDef
    , toplevelprocess
    , equivLemma
    , diffEquivLemma
)
where

import           Prelude                    hiding (id, (.))
import qualified Data.ByteString.Char8      as BC
import           Data.Label
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           Control.Applicative        hiding (empty, many, optional)
-- import qualified Control.Monad.Catch        as Catch
import           Text.Parsec                hiding ((<|>))
import           Theory
import           Theory.Sapic
import           Theory.Text.Parser.Token

import           Theory.Text.Parser.Term
import           Theory.Text.Parser.Fact
import           Theory.Text.Parser.Rule
import Theory.Text.Parser.Let
import Theory.Text.Parser.Formula
import Theory.Sapic.Pattern
import qualified Data.Functor.Identity ()
import Data.Maybe (fromMaybe)


-- used for debugging
-- println :: String -> ParsecT String u Identity ()
-- println str = traceShowM str

-- | Parse a lit with logical typed variables for SAPIC
ltypedlit :: Parser SapicTerm
ltypedlit = vlit sapicvar

-- | Parse a lit with logical typed variables and pattern matching for SAPIC
ltypedpatternlit :: Parser (SapicNTerm PatternSapicLVar)
ltypedpatternlit = vlit sapicpatternvar

-- | Parse a variable in SAPIC that is typed
sapicterm :: Parser (Term (Lit Name SapicLVar))
sapicterm = msetterm False ltypedlit

-- | Parse a sapic pattern
sapicpatternterm :: Parser (Term (Lit Name PatternSapicLVar))
sapicpatternterm = msetterm False ltypedpatternlit

-- | parse a process definition (let P = .. ) or (let P (v1,...,vn) = ..)
processDef :: OpenTheory -> Parser ProcessDef
processDef thy= do
                i <- try $ do
                    _ <- letIdentifier
                    BC.pack <$> identifier
                vs <- optionMaybe $ parens $ commaSep sapicvar
                equalSign
                p <- process thy
                return (ProcessDef (BC.unpack i) p vs)

toplevelprocess :: OpenTheory -> Parser PlainProcess
toplevelprocess thy = do
                    _ <- try (symbol "process")
                    _ <- colon
                    process thy
                    <?> "top-level process"

-- | Parse a single sapic action, i.e., a thing that can appear before the ";"
-- (This includes almost all items that are followed by one instead of two
-- processes, the exception is replication)
sapicAction :: Parser (LSapicAction, ProcessParsedAnnotation)
sapicAction = (do
                        _ <- try $ symbol "new"
                        s <- sapicvar
                        return (New s,mempty)
              )
               <|> (do -- insert must appear before in to not confuse the parser
                        _ <- try $ symbol "insert"
                        t <- msetterm False ltypedlit
                        _ <- comma
                        t' <- msetterm False ltypedlit
                        return (Insert t t', mempty)
                   )
               <|> (do
                        _ <- try $ symbol "in"
                        _ <- symbol "("
                        (maybeChannel,pt) <-
                            try (do
                                pt <- msetterm False ltypedpatternlit
                                _ <- symbol ")"
                                return (Nothing,pt)
                                )
                            <|>(do
                                c <- msetterm False ltypedlit
                                _ <- comma
                                pt<- msetterm False ltypedpatternlit
                                _ <- symbol ")"
                                return (Just c, pt)
                                )
                        if validPattern S.empty pt -- only validate that freshly bound variables do not intersect with matches.
                            then return (ChIn maybeChannel (unpattern pt) (extractMatchingVariables pt), mempty)
                            else fail $ "Invalid pattern: " ++ show pt
                   )
               <|> (do
                        _ <- try $ symbol "out"
                        _ <- symbol "("
                        (maybeChannel,t) <-
                            try (do
                                t <- msetterm False ltypedlit
                                _ <- symbol ")"
                                return (Nothing,t))
                            <|>(do
                                t <- msetterm False ltypedlit
                                _ <- comma
                                t' <- msetterm False ltypedlit
                                _ <- symbol ")"
                                return (Just t, t')
                                )
                        return (ChOut maybeChannel t, mempty)
                   )
               <|> (do
                        _ <- try $ symbol "delete"
                        t <- msetterm False ltypedlit
                        return (Delete t, mempty)
                   )
               <|> (do
                        _ <- try $ symbol "lock"
                        t <- msetterm False ltypedlit
                        return (Lock t, mempty)
                   )
               <|> (do
                        _ <- try $ symbol "unlock"
                        t <- msetterm False ltypedlit
                        return (Unlock t, mempty)
                   )
               <|> (do
                        _ <- try $ symbol "event"
                        f <- fact ltypedlit
                        return (Event f, mempty)
                   )
               <|> (do
                        (l,a,r,phi) <- try $ genericRule sapicpatternvar (PatternBind <$> sapicnodevar)
                        let matchVars =  foldMap (foldMap extractMatchingVariables) l
                        let f = fmap (fmap unpattern)
                        let g = fmap (fmap unpatternVar)
                        if validMSR S.empty (l,a,r) -- only validate that freshly bound variable do not intersect with matches.
                            then return (MSR (f l) (f a) (f r) (g phi) matchVars, mempty)
                            else fail $ "Invalid pattern in lhs of embedded MSR: " ++ show l
                   )

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
process :: OpenTheory -> Parser PlainProcess
process thy=
            -- left-associative NDC and parallel using chainl1.
            -- Note: this roughly encodes the following grammar:
            -- <|>   try   (do
            --             p1 <- actionprocess thy
            --             opParallel
            --             p2 <- process thy
            --             return (ProcessParallel p1 p2))
                  chainl1 (actionprocess thy) (
                             do { _ <- try opNDC; return (ProcessComb NDC mempty)}
                         <|> do { _ <- try opParallelDepr; return (ProcessComb Parallel mempty)}
                         <|> do { _ <- opParallel; return (ProcessComb Parallel mempty)}
                  )

equivLemma :: OpenTheory -> Parser TranslationElement
equivLemma thy = do
               _ <- try $ symbol "equivLemma"
               _ <- colon
               p1 <- process thy
               p2 <- process thy
               return $ EquivLemma p1 p2

diffEquivLemma :: OpenTheory -> Parser TranslationElement
diffEquivLemma thy = do
               _ <- try $ symbol "diffEquivLemma"
               _ <- colon
               modifyStateSig (`mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
               p <- process thy
               return $ DiffEquivLemma p


elseprocess :: OpenTheory
    -> Parser PlainProcess
elseprocess thy = option (ProcessNull mempty) (symbol "else" *> process thy)

actionprocess :: OpenTheory -> Parser PlainProcess
actionprocess thy=
                (do     -- replication parser
                        _ <- try $ symbol "!"
                        p <- process thy
                        return (ProcessAction Rep mempty p)
                        <?> "replication"
                )
            <|> (do     -- lookup / if with and w/o else branches
                        _ <- try $ symbol "lookup"
                        t <- sapicterm
                        _ <- symbol "as"
                        v <- sapicvar
                        _ <- symbol "in"
                        p <- process thy
                        q <- elseprocess thy
                        return (ProcessComb (Lookup t v) mempty p q)
                        <?> "lookup process"
                   )
            <|> (do
                        _ <- try $ symbol "if"
                        cond <- try (do
                                t1 <- sapicterm
                                _ <- opEqual
                                t2 <- sapicterm
                                return (CondEq t1 t2)
                                <?> "equality between two terms"
                                )
                               <|> (do
                                frml <- standardFormula sapicvar sapicnodevar
                                return (Cond frml)
                                )
                        _ <- symbol "then"
                        p <- process thy
                        q <- elseprocess thy
                        return (ProcessComb cond mempty p q)
                        <?> "conditional process"
                   )
            <|>    (do -- let expressions:
                        _  <- try $ letIdentifier
                        ls  <-genericletBlock sapicpatternterm sapicterm
                        _  <- symbol "in"
                        p   <- process thy
                        q   <- elseprocess thy
                        let f (t1,t2) p' =
                                    ProcessComb (Let (unpattern t1) t2 (extractMatchingVariables t1)) mempty p' q
                        return $ foldr f p ls
                        <?> "let binding"
                )
            <|> (do   -- null process: terminating element
                        _ <- try opNull
                        return (ProcessNull mempty) )
            <|> ( do  -- sapic actions are separated by ";"
                      -- but allow trailing actions (syntactic sugar for action; 0)
                        (s,ann) <- try sapicAction
                        p <-  option (ProcessNull mempty) (try opSeq *> actionprocess thy)
                        return (ProcessAction s ann p))
            <|>  (do    -- combined parser for `(p)` and `(p)@t`
                        _ <- try $ symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        p' <- (do
                                _ <- try $ symbol "@"
                                m <- sapicterm
                                return $ processAddAnnotation p (mempty {location = (Just m)})
                               )
                              <|> (return p)
                        return p'
                 )
            <|> try (do -- parse identifier
                        -- println ("test process identifier parsing Start")
                        i <- BC.pack <$> identifier
                        ts <- option [] $ parens $ commaSep (msetterm False ltypedlit)
                        (p, vars) <- checkProcess (BC.unpack i) thy
                        let base_subst = zip vars ts
                        let extend_sup = foldl (\acc (svar,t) ->
                                  map (,t)
                                   (case svar of
                                      (SapicLVar sl_var (Just _)) ->
                                        [svar, SapicLVar sl_var Nothing]
                                      _ -> [svar]
                                   )
                                  ++ acc) [] base_subst
                        substP <- applyM (substFromList extend_sup) p
                        return (ProcessComb
                                (ProcessCall (BC.unpack i) ts) mempty
                                (processAddAnnotation substP (mempty {processnames =  [BC.unpack i]}))
                                (ProcessNull mempty))
                        )
-- | checks if process exists, if not -> error
checkProcess :: String -> OpenTheory -> Parser (PlainProcess, [SapicLVar])
checkProcess i thy = case lookupProcessDef i thy of
    Just p -> return (get pBody p, fromMaybe [] $ get pVars p)
    Nothing -> fail $ "process not defined: " ++ i
