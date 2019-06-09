{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute translation-specific restrictions
module Sapic.Accountability (
      generateAccountabilityLemmas
) where
import           Control.Monad
import           Control.Monad.Catch
import           Control.Arrow
-- import qualified Data.List              as List
-- import qualified Data.Monoid            as M
import qualified Data.Set               as S
-- import           Data.Typeable
import qualified Extension.Data.Label   as L
import           Sapic.Annotation
import           Sapic.Exceptions
-- import           Sapic.Facts
-- import           Text.Parsec.Error           
-- import           Text.RawString.QQ
import           Theory
-- import           Theory.Sapic
-- import           Theory.Text.Parser

import           Extension.Prelude

-- | Create a lemma from a formula with quantifier. Copies accLemma's name
-- (plus suffix) and attributes.
toLemma :: AccLemmaGeneral c -> TraceQuantifier -> ([Char], LNFormula) -> Lemma ProofSkeleton
toLemma accLemma quantifier (suffix,formula)  = 
        skeletonLemma (L.get aName accLemma ++ suffix) (L.get aAttributes accLemma) quantifier formula (unproven ())

-- | Obtain case names used in Lemma
caseNames :: AccLemmaGeneral [CaseTest] -> [CaseIdentifier]
caseNames accLemma = map (L.get cName) (L.get aCaseTests accLemma)

-- | Quantify all free variables after removing duplicates and sorting them.
quantifyFrees :: LNFormula -> LNFormula
quantifyFrees fm = foldr (\(h, v) -> exists h v) fm hintedVars
    where hintedVars = map (\s -> ((lvarName s, lvarSort s), s)) (freesList fm)

-- | Conjunction of corrupt events off the parties in the argument list
-- | TODO: - Replace 'pubTerm' with ??
-- |       - How to avoid 'True' atom? 
corruptParties :: [LVar] -> LNFormula
corruptParties parties = foldl (.&&.) (TF True) corrupted
    where
        corrupted = map (\p -> (Ato (Action (pubTerm "0") (Fact {factTag = ProtoFact Linear "Corrupted" 1, factAnnotations = S.empty, factTerms = [varTerm $ Free p]})))) parties
-- | (Ato (Action Bound 0 (Fact {factTag = ProtoFact Linear "Corrupted" 1, factAnnotations = fromList [], factTerms = [varTerm (Free $ A)]}))))

-- | Exclusiveness of ψ_1,..: not (ψ_i && ψ_j) for all i≠j ) 
exclusiveness :: AccLemma -> [Lemma ProofSkeleton]
exclusiveness accLemma  = map (toLemma accLemma AllTraces) unequals
    where
        unequals = [ (suff id_i id_j ,f phi_i phi_j) 
                                   | (id_i,phi_i) <- get accLemma 
                                    ,(id_j,phi_j) <- get accLemma
                                    , id_i /= id_j
                                    ]
        get l = map (L.get cName &&& L.get cFormula)  (fst $ L.get aCaseTests l)
        suff id1 id2 = "_excl_" ++ id1 ++ id2
        f phi1 phi2 = Not (phi1 .&&. phi2) -- TODO bind free names, how?

-- | Minimiality for singleton
-- | For all traces t: ∀ S' ⊆ fv(ψ_i). not(ψ_i ∧ corrupted(t) = S')
minimalitySingleton :: AccLemma -> [Lemma ProofSkeleton]
minimalitySingleton accLemma = map (toLemma accLemma AllTraces) implies
    where
        implies = [ (suff id_i parties, f phi_i parties)
                                   | (id_i, phi_i) <- get accLemma
                                   , parties <- powerset $ frees phi_i ]
        powerset = filterM (const [True,False])
        get l = map (L.get cName &&& L.get cFormula)  (fst $ L.get aCaseTests l)
        suff id parties = "_min_" ++ id ++ (show parties)
        f phi parties = Not (phi .&&. (corruptParties parties))

-- | Verifiability of ψ_i -> fv(ψ_i) and fv(ψ_i) empty
-- | For all traces t: ψ_i ⇒ φ(t).
verifiabilityEmpty :: AccLemma -> [Lemma ProofSkeleton]
verifiabilityEmpty accLemma = map (toLemma accLemma AllTraces) implies
    where
        implies = [ (suff id_i, f phi_i) | (id_i, phi_i) <- get accLemma, null $ freesList phi_i ]
        get l = map (L.get cName &&& L.get cFormula)  (fst $ L.get aCaseTests l)
        suff id = "_ver_empty_" ++ id
        f phi = phi .==>. L.get aFormula accLemma

-- | Verifiability of ψ_i -> fv(ψ_i) and fv(ψ_i) non-empty
-- | For all traces t: ψ_i ⇒ ¬φ(t).
verifiabilityNonempty :: AccLemma -> [Lemma ProofSkeleton]
verifiabilityNonempty accLemma = map (toLemma accLemma AllTraces) implies
    where
        implies = [ (suff id_i, f phi_i) | (id_i, phi_i) <- get accLemma, not $ null $ freesList phi_i ]
        get l = map (L.get cName &&& L.get cFormula)  (fst $ L.get aCaseTests l)
        suff id = "_ver_nonempty_" ++ id
        f phi = phi .==>. Not (L.get aFormula accLemma)

-- | Sufficiency for singleton
-- | Exists trace t: ψ_i ∧ ¬φ(t) ∧ corrupt(t) = fv(ψ_i)
-- | TODO: How to combine #i #j in the different formulas?
sufficiencySingleton :: AccLemma -> [Lemma ProofSkeleton]
sufficiencySingleton accLemma = map (toLemma accLemma ExistsTrace) implies
    where
        implies = [ (suff id_i, f phi_i) | (id_i, phi_i) <- get accLemma ]
        get l = map (L.get cName &&& L.get cFormula)  (fst $ L.get aCaseTests l)
        suff id = "_suf_" ++ id
        f phi = phi .&&. Not (L.get aFormula accLemma) .&&. (corruptParties $ frees phi)

-- | Uniqueness
-- | For all traces t: ψ_i ⇒ corrupt(t) = fv(ψ_i)
uniquenessSingleton :: AccLemma -> [Lemma ProofSkeleton]
uniquenessSingleton accLemma = map (toLemma accLemma AllTraces) implies
    where
        implies = [ (suff id_i, f phi_i) | (id_i, phi_i) <- get accLemma ]
        get l = map (L.get cName &&& L.get cFormula)  (fst $ L.get aCaseTests l)
        suff id = "_uniq_" ++ id
        f phi = phi .==>. (corruptParties $ frees phi)

casesAxioms :: AccLemma -> [Lemma ProofSkeleton]
casesAxioms accLemma = 
        exclusiveness accLemma
        ++
        verifiabilityEmpty accLemma
        ++
        verifiabilityNonempty accLemma
        ++
        sufficiencySingleton accLemma
        ++
        minimalitySingleton accLemma
        ++
        uniquenessSingleton accLemma
        -- (exclusiveness id op vf )
        -- @
        -- [exhaustiveness id op vf]
        -- @
        -- (sufficiencySingleton id op parties vf phi)
        -- @
        -- (sufficiencyComposite id rel vf)
        -- @
        -- (verifiability_empty id op vf phi)
        -- @
        -- (verifiability_nonempty id op vf phi)
        -- @
        -- (minimalitySingleton id op rel parties vf phi)
        -- @
        -- (minimalityComposite id rel vf)
        -- @
        -- (uniquenessSingleton id op vf)
        -- @ 
        -- (completenessComposite id rel vf) (*Not actually needed, parser takes care of that *)
        -- (* Reflexivity and termination are guaranteed by parser, too. *)

generateAccountabilityLemmas :: (Monad m, MonadThrow m) => AccLemma -> m [Lemma ProofSkeleton]
generateAccountabilityLemmas accLemma = do
    return (casesAxioms accLemma)
    -- | Coarse <- L.get aAccKind accLemma = return []
    -- | Cases <- L.get aAccKind  accLemma = return $ cases_axioms accLemma 
    --     -- (cases_axioms id op parties vf phi)
    --     -- @
    --     -- (relationLifting manualf id op vf rel)
    -- | ControlEquivalence <- L.get aAccKind accLemma = return []
