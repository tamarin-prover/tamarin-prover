-- Copyright   : (c) 2019-2021 Robert Künnemann, Kevin Morio & Yavor Ivanov
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from OpenTheories to OpenTheories with accountability lemmas

module Accountability (
       module Accountability.Generation
     , translate
) where
import Control.Monad.Catch (MonadThrow (throwM), MonadCatch, Exception)
import Theory (OpenTheory, CaseIdentifier, theoryAccLemmas, aCaseIdentifiers, cName, aName, aCaseTests, AccLemma, caseTestToPredicate, theoryCaseTests)
import Data.Data (Typeable)
import Control.Applicative (Alternative)
import qualified Data.Label as L
import Data.List (intercalate, (\\))
import Data.Maybe (mapMaybe)
import Control.Monad (unless, guard, foldM)
import Accountability.Generation (generateAccountabilityLemmas)
import Theory.Text.Parser (liftedAddLemma)
import Theory.Text.Parser.Signature (liftedAddPredicate)


------------------------------------------------------------------------------
-- Translating open theories containing accountability lemmas
------------------------------------------------------------------------------

-- | Datatype for accountability exceptions. See the instances for explanations.
newtype AccException = 
    CaseTestsUndefined [(String, [CaseIdentifier])] 
    deriving (Typeable)

instance Show AccException where
    show (CaseTestsUndefined el) =
        "The following case tests are undefined but are required in a lemma: \n" ++
        intercalate "\n" (fmap (\(a, c) -> "  '" ++ intercalate "', '" c ++ "' required by lemma '" ++ a ++ "'") el)
instance Exception AccException

-- | Translates the accountability lemmas in an open theory 
translate :: (Monad m, MonadThrow m, MonadCatch m) => OpenTheory -> m OpenTheory
translate thy = do
    let undef = mapMaybe undefinedCaseTests (theoryAccLemmas thy)
    unless (null undef) (throwM (CaseTestsUndefined undef :: AccException))
    accLemmas <- mapM generateAccountabilityLemmas (theoryAccLemmas thy)
    thy' <- foldM liftedAddLemma thy (concat accLemmas)
    let casePredicates = mapMaybe caseTestToPredicate (theoryCaseTests thy)
    foldM liftedAddPredicate thy' casePredicates


-- | Checks if the case tests requiered by an accountability lemma are present
undefinedCaseTests :: Alternative f => AccLemma -> f (String, [CaseIdentifier])
undefinedCaseTests accLem = (L.get aName accLem, required \\ defined) <$ guard (required /= defined)
    where
        required =  L.get aCaseIdentifiers accLem
        defined = map (L.get cName) (L.get aCaseTests accLem)
