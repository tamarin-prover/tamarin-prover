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
import           Control.Monad.Catch
import           Control.Arrow
-- import qualified Data.List              as List
-- import qualified Data.Monoid            as M
-- import qualified Data.Set               as S
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

-- | Create a lemma from a formula with quantifier. Copyies accLemma's name
-- (plus suffix) and attributes.
toLemma :: AccLemmaGeneral c -> TraceQuantifier -> ([Char], LNFormula) -> Lemma ProofSkeleton
toLemma accLemma quantifier (suffix,formula)  = 
        skeletonLemma (L.get aName accLemma ++ suffix) (L.get aAttributes accLemma) quantifier formula (unproven ())

-- | Obtain case names used in Lemma
caseNames :: AccLemmaGeneral [CaseTest] -> [CaseIdentifier]
caseNames accLemma = map (L.get cName) (L.get aCaseTests accLemma)

-- | Exclusiveness of φ_1,..: not (φ_i && φ_j) for all i≠j ) 
exclusiveness :: AccLemma -> [Lemma ProofSkeleton]
exclusiveness accLemma  = map (toLemma accLemma AllTraces) unequals
    where
        unequals = [ (suff id_i id_j ,f phi_i phi_j) 
                                   | (id_i,phi_i) <- get accLemma 
                                    ,(id_j,phi_j) <- get accLemma
                                    , id_i /= id_j
                                    ]
        get l = map (L.get cName &&& L.get cFormula)  (fst $ L.get aCaseTests l)
        suff id1 id2 = "excl_"++id1++id2
        f phi1 phi2 =  Not (phi1 .&&. phi2) -- TODO bind free names

cases_axioms :: AccLemma -> [Lemma ProofSkeleton]
cases_axioms accLemma = exclusiveness accLemma 
                     -- ++ []
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
generateAccountabilityLemmas accLemma = throwM ( (NotImplementedError "lol"):: SapicException AnnotatedProcess)
    -- | Coarse <- L.get aAccKind accLemma = return []
    -- | Cases <- L.get aAccKind  accLemma = return $ cases_axioms accLemma 
    --     -- (cases_axioms id op parties vf phi)
    --     -- @
    --     -- (relationLifting manualf id op vf rel)
    -- | ControlEquivalence <- L.get aAccKind accLemma = return []
