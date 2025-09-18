-- |
-- Copyright   : (c) 2019 Charlie Jacomme <charlie.jacomme@lsv.fr>
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for always-secret channels
--
-- A channel is defined always-secret iff it correspond to a fresh variable
-- only use as a channel identifier. For these channels, we can use a more
-- efficient translation, as the adversary can never deduce then, and thus only
-- a silent transition is possible.

module Sapic.Report
  ( translateTermsReport
  , reportInit
  ) where

import Data.Set as S
import Data.List as L
import Sapic.Annotation
import Sapic.Facts
import Theory
import Theory.Sapic
import Term.Builtin.Signature

reportInit ::  Monad m => LProcess ann -> ([AnnotatedRule ann], Set LVar) -> m ([AnnotatedRule ann], Set LVar)
reportInit anP (initrules,initTx) = return (reportrule : initrules, initTx)
  where
        reportrule = AnnotatedRule (Just "ReportRule") anP (Right NoPosition)
                    [In $ fAppPair (varTerm x,varTerm loc)] -- prem
                    []
                    [Out $ fAppNoEq repSym [varTerm x, varTerm loc]]
                    [Ato protFact]
                    0
        var s = LVar s LSortMsg 0
        x = var "x"
        loc = var "loc"
        -- protFact =  Syntactic . Pred $ (protoFact Linear "Report" [varTerm x, varTerm loc])
        protFact =  Syntactic . Pred $ protoFact Linear "Report" [varTerm (Free x), varTerm (Free loc)]

-- | This rules use the builtin restriction system to bind the Report predicate (which must be defined by the user), to this rule.
opt_loc :: Maybe SapicTerm -> ProcessAnnotation v -> Maybe SapicTerm
opt_loc loc ann =
 case location ann.parsingAnn of
  Nothing -> loc
  Just x -> Just x

reportMapTerms :: (Maybe SapicTerm -> SapicTerm -> SapicTerm)
            -> Maybe SapicTerm
            -> LProcess (ProcessAnnotation LVar)
            -> LProcess (ProcessAnnotation LVar)
reportMapTerms _ _  (ProcessNull ann)  = ProcessNull ann
reportMapTerms f loc (ProcessAction ac ann p') = ProcessAction (reportMapTermsAction f (opt_loc loc ann) ac) ann
  $ reportMapTerms f (opt_loc loc ann) p'
reportMapTerms f loc (ProcessComb c ann pl pr) = ProcessComb (reportMapTermsComb f (opt_loc loc ann) c) ann
  (reportMapTerms f (opt_loc loc ann) pl)
  (reportMapTerms f (opt_loc loc ann) pr)
reportMapTermsAction :: (Maybe SapicTerm -> SapicTerm -> SapicTerm)
            -> Maybe SapicTerm
  -> LSapicAction
            -> LSapicAction
reportMapTermsAction f loc ac
        | (New v) <- ac = New v -- (f loc) is always the identity over variables
        | (ChIn  mt t vs) <- ac   = ChIn (fmap (f loc) mt) (f loc t) vs
        | (ChOut mt t) <- ac   = ChOut (fmap (f loc) mt) (f loc t)
        | (Insert t1 t2) <- ac = Insert (f loc t1) (f loc t2)
        | (Delete t) <- ac     = Delete (f loc t)
        | (Lock t) <- ac       = Lock (f loc t)
        | (Unlock t) <- ac     = Unlock (f loc t)
        | (Event fa) <- ac      = Event (fmap (f loc) fa)
        | (MSR l a r rest vs) <- ac  = MSR (f2mapf l) (f2mapf a) (f2mapf r) (fmap formulaMap rest) vs
        |  Rep <- ac            = Rep
            where f2mapf = fmap $ fmap (f loc)
                  -- something like
                  -- formulaMap = mapAtoms $ const $ fmap $ fmap f
                  formulaMap = undefined
reportMapTermsComb:: (Maybe SapicTerm -> SapicTerm -> SapicTerm)
            -> Maybe SapicTerm
            -> ProcessCombinator SapicLVar
            -> ProcessCombinator SapicLVar
reportMapTermsComb f loc c
        | (Cond _) <- c = Cond $ undefined -- same problem as above
        | (CondEq t1 t2) <- c = CondEq (f loc t1) (f loc t2)
        | (Let t1 t2 vs) <- c = Let (f loc t1) (f loc t2) vs
        | (Lookup t v) <- c = Lookup (f loc t) v
        | otherwise = c

subst :: Maybe SapicTerm -> SapicTerm -> SapicTerm
subst Nothing t = t
subst (Just loc) t = case viewTerm t of
  Lit _ -> t
  FApp (NoEq sym) [a] -> if sym == reportSym then
                                termViewToTerm $ FApp (NoEq repSym)  [subst (Just loc) a, loc]
                         else t
  FApp k as -> termViewToTerm $ FApp k (L.map (subst (Just loc)) as)

translateTermsReport :: LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
translateTermsReport = reportMapTerms subst Nothing
