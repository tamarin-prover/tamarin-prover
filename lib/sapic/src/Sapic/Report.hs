{-# LANGUAGE PatternGuards #-}
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

module Sapic.Report (
    translateTermsReport
    , reportInit
) where
-- import           Control.Exception
-- import           Control.Monad.Catch
-- import           Control.Monad.Fresh
import           Data.Set as S
import           Data.List as L
import           Sapic.Annotation
import           Sapic.Facts
-- import           Sapic.Exceptions
import           Theory
import           Theory.Sapic
import           Term.Builtin.Signature

reportInit ::  Monad m => AnProcess ann -> ([AnnotatedRule ann], Set LVar) -> m ([AnnotatedRule ann], Set LVar)
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
        protFact =  Syntactic . Pred $ (protoFact Linear "Report" [varTerm (Free x), varTerm (Free loc)])
-- This rules use the builtin restriction system to bind the Report predicate (which must be defined by the user), to this rule.

opt_loc :: Maybe SapicTerm -> ProcessAnnotation -> Maybe SapicTerm
opt_loc loc ann =
 case (location ann) of
  Nothing -> loc
  Just x -> Just x

mapTerms :: (Maybe SapicTerm -> SapicTerm -> SapicTerm)
            -> Maybe SapicTerm
            -> AnProcess ProcessAnnotation
            -> AnProcess ProcessAnnotation
mapTerms _ _  (ProcessNull ann)  = ProcessNull ann
mapTerms f loc (ProcessAction ac ann p') = ProcessAction (mapTermsAction f (opt_loc loc ann) ac) ann
  $ mapTerms f (opt_loc loc ann) p'
mapTerms f loc (ProcessComb c ann pl pr) = ProcessComb (mapTermsComb f (opt_loc loc ann) c) ann
  (mapTerms f (opt_loc loc ann) pl)
  (mapTerms f (opt_loc loc ann) pr)
mapTermsAction :: (Maybe SapicTerm -> SapicTerm -> SapicTerm)
            -> Maybe SapicTerm
            -> SapicAction
            -> SapicAction
mapTermsAction f loc ac
        | (New v) <- ac, v' <- termVar' (f loc (varTerm v)) = New v'
        | (ChIn  mt t) <- ac   = ChIn (fmap (f loc) mt) (f loc t)
        | (ChOut mt t) <- ac   = ChOut (fmap (f loc) mt) (f loc t)
        | (Insert t1 t2) <- ac = Insert (f loc t1) (f loc t2)
        | (Delete t) <- ac     = Delete (f loc t)
        | (Lock t) <- ac       = Lock (f loc t)
        | (Unlock t) <- ac     = Unlock (f loc t)
        | (Event fa) <- ac      = Event (fmap (f loc) fa)
        | (MSR (l,a,r,rest)) <- ac  = MSR $ (f2mapf l, f2mapf a, f2mapf r, fmap formulaMap rest)
        |  Rep <- ac            = Rep
            where f2mapf = fmap $ fmap (f loc)
                  -- something like
                  -- formulaMap = mapAtoms $ const $ fmap $ fmap f
                  formulaMap = undefined
mapTermsComb:: (Maybe SapicTerm -> SapicTerm -> SapicTerm)
            -> Maybe SapicTerm
            -> ProcessCombinator
            -> ProcessCombinator
mapTermsComb f loc c
        | (Cond _) <- c = Cond $ undefined -- same problem as above
        | (CondEq t1 t2) <- c = CondEq (f loc t1) (f loc t2)
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

translateTermsReport :: AnProcess ProcessAnnotation -> AnProcess ProcessAnnotation
translateTermsReport = mapTerms subst Nothing
