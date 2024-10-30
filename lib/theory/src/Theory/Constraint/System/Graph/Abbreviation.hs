{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE ViewPatterns #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- This implements generating abbreviations for a given graph representation.
-- The abbreviations are computed from all LNTerm's in the graph and the method is based on cleandot.py 
-- All terms in the graph are weighted based on their multiplicity and length, highest weighted terms are abbreviated first.
-- The abbreviation itself is based on the string representation of a term. 
-- E.g. Function(a,b,c) => FU1
module Theory.Constraint.System.Graph.Abbreviation (
    Abbreviations
  , lookupAbbreviation
  , computeAbbreviations
  , AbbreviationOptions(..)
  , AbbreviationTerm
  , AbbreviationExpansion
  , defaultAbbreviationOptions
  , applyAbbreviationsFact
  , applyAbbreviationsTerm
  ) where

import           Data.Char                (isAlphaNum, toUpper, isAlpha)
import qualified Data.Text                as T
import qualified Data.Map                 as M
import           Data.Maybe
import qualified Data.Ord                 
import qualified Data.ByteString.Char8 as BC
import           Data.List                (sort, nub, mapAccumL)
import           Extension.Data.Label
import           Extension.Prelude
import           Text.PrettyPrint.Class
import           Theory.Constraint.System.Graph.GraphRepr
import           Term.LTerm
import           Theory                   (LNFact, rPrems, rConcs, rActs, factTerms)
import Debug.Trace.EnvTracer (etraceSectionLn, etraceLn)

-- | Type for the abbreviation itself, which is always a literal containing the string representation.
type AbbreviationTerm = LNTerm
-- | Type for the expanded abbreviation, which is the original term where subterms are replaced by other abbreviations where possible.
type AbbreviationExpansion = LNTerm
-- | Abbreviations are represented as a map from the original LNTerm 
-- to the abbreviated LNTerm and the original LNTerm where all existing
-- abbreviations have already been applied.
-- ==== __Example__:
--   [ Function1(a,b)              => Fun1, Function1(a,b)
--   , Function2(Function1(a,b),c) => Fun2, Function2(Fun1,c)
--   ]
type Abbreviations = M.Map LNTerm (AbbreviationTerm, AbbreviationExpansion)

type Weight = Int
-- | Options to control the abbreviation generation.
data AbbreviationOptions = AbbreviationOptions 
  { aoAbbrevsSoftLimit   :: Int    -- ^ The soft limit of how many abbreviations to generate if the term weight is not greater or equal than 'aoAlwaysAbbrevWeight'.
  , aoAlwaysAbbrevWeight :: Weight -- ^ Terms that have weight greater or equal to this always generate an abbreviation even if the number of abbreviations is greater than 'aoAbbrevsSoftLimit'.
  , aoFirstIndex         :: Int    -- ^ The first index to use when generating abbreviations.
  , aoPrefixLength       :: Int    -- ^ The length of an abbreviation prefixes.
  }
  deriving( Eq, Ord )


-- | The default abbreviation options.
defaultAbbreviationOptions :: AbbreviationOptions
defaultAbbreviationOptions = AbbreviationOptions 
  { aoAbbrevsSoftLimit = 10
  , aoAlwaysAbbrevWeight = 30 -- a.d. TODO what is a good default value for this?
  , aoFirstIndex = 1
  , aoPrefixLength = 2
  }

-- | Lookup a single term in an abbreviations map and return the abbreviation name.
lookupAbbreviation :: Abbreviations -> LNTerm -> Maybe AbbreviationTerm
lookupAbbreviation abbrevs t = fst <$> M.lookup t abbrevs

-- | Weigh each term based on its size and how often it appears in the graph.
judgeTerm :: M.Map LNTerm LNTerm -- ^ The existing set of abbreviations used to compute the screen size of the current term under consideration.
          -> LNTerm              -- ^ The current term to consider for abbreviating.
          -> (Int, [Int])        -- ^ The total number of occurrences and a list where each element is the number of occurrences in the existing set of abbreviations.
          -> Weight              -- ^ The resulting weight we give to that abbreviation.
judgeTerm abbrevs t (occs, legendOccs) 
  | termWeight < 10 = -1
  | relativeOccs <= 1 = -1
  | otherwise = relativeOccs * termWeight
  where
    -- | The termsize is the length of the term rendered as a string.
    termWeight :: Weight
    termWeight = 
      let replacedTerm = applyAbbreviationsTerm (\k -> M.lookup k abbrevs) t in
      length $ render $ prettyLNTerm replacedTerm
    
    -- | A "relative" occurrence is computed by comparing the total number of occurrences
    -- with the number of occurrences only in the legend.
    -- If we find the only occurrence of a term only in the legend then we will never abbreviate it.
    relativeOccs :: Int
    relativeOccs = 
      if occs == 1 && legendOccs == [1]
      then 0
      else occs

-- | Find a suitable abbreviation prefix for the given term in upper-case.
-- For a literal we take the first 2 characters and for function symbols we either special-case the name or also take the first 2 characters.
-- If more fine-grained control is needed we can use viewTerm2 instead of viewTerm.
getTermPrefix :: AbbreviationOptions -> LNTerm -> String
getTermPrefix options t = map toUpper $ take (aoPrefixLength options) $ filter isAlpha go
  where
    go = case viewTerm t of
         Lit l                  -> show l
         FApp   (NoEq (s,_)) _  -> BC.unpack s
         -- a.d. TODO what is a good abbreviation for the "emap"?
         FApp   (C _) _         -> "EMP"
         FApp   List _          -> "LST"
         FApp   (AC o) _        -> show o


type PrefixMap = M.Map String Int

-- | For a given term `t`, find a suitable abbreviation and update the prefix index map.
-- The prefixMap maps a prefix to the next possible index candidate.
abbreviateTerm :: AbbreviationOptions -> [String] -> PrefixMap -> LNTerm -> (PrefixMap, LNTerm)
abbreviateTerm options allNames prefixMap t = 
  let pref = getTermPrefix options t
      idxCandidate = getIndexCandidate pref in
    go pref idxCandidate
  where
    -- | Try out successive index candidates to create an abbreviation. 
    -- For each candidate we create the abbreviation and check if it is contained in the global map.
    -- If it already exists we try the next index candidate.
    go :: String -> Int -> (PrefixMap, LNTerm)
    go pref idxCandidate = 
      let nameCandidate = pref ++ show idxCandidate 
          idxCandidateNext = idxCandidate + 1 in
      if nameCandidate `elem` allNames 
      then go pref idxCandidateNext
      else (M.insert pref idxCandidateNext prefixMap, var nameCandidate)

    -- | Check the prefix index map for a suitable index for the given prefix.
    getIndexCandidate :: String -> Int
    getIndexCandidate pref = fromMaybe (aoFirstIndex options) $ M.lookup pref prefixMap 
        
    -- | Create a variable from some prefix and index. 
    -- We append the index to the string directly instead of using the variable index since 
    -- the variable renderer inserts a point between name and index.
    var :: String -> LNTerm
    var name = 
      let  in
      lit $ Var $ LVar name LSortMsg 0
    

-- | For a given graph representation, compute possible abbreviations that can be applied.
-- Abbreviations are always LNTerm variables with a differentiating number suffix.
--
-- actually what would lead to the best abbreviations is:
--   calculate terms + occurrences
--   calculate weights
--   take term X with maximum weight and make abbreviation
--   now for each subterm of X, decrement its occurrence (this can be reasonable fast if we keep the allTermOccs and just delete X, then go through all its subterms and decrement them)
--     this is good in a situation where 
--   for each other term that has X as a subterm, reduce replace X by its abbreviation when calculating the term size (this can be made fast by keeping around the list of abbreviations and applying it to each expression when calculating the term size)
--     this is good in a situation where you have a term X = F(Y) where Y has bigger weight than X and is abbreviated first. When Y is replaced by an abbreviation the weight of X drops a lot and probably does not need to be abbreviated.
--   repeat finding the next term with maximum weight
--   This algorithm is probably cubic in the number of terms, as finding all subterms is already quadratic and now we do this for each term.
    
computeAbbreviations :: GraphRepr -> AbbreviationOptions -> Abbreviations 
computeAbbreviations repr options = makeRecursive $ M.toList $ go allTermOccs M.empty M.empty
  where
    go :: M.Map LNTerm (Int, [Int]) -> PrefixMap -> M.Map LNTerm LNTerm -> M.Map LNTerm LNTerm
    go termOccs prefixMap abbrevs = 
      let weightedTerms = M.mapWithKey (judgeTerm abbrevs) termOccs
          candidateM = filterCandidateTerm $ M.toList weightedTerms
      in
        case candidateM of
          Nothing -> abbrevs
          Just (candidate, weight) -> 
            -- If the candidate weight is too low and we already have enough abbreviations, return the current abbreviations.
            if weight < aoAlwaysAbbrevWeight options && length abbrevs >= aoAbbrevsSoftLimit options
            then abbrevs
            else 
              -- make an abbreviation for this term
              let (newPrefixMap, abbrevName) = abbreviateTerm options allNames prefixMap candidate
                  -- Delete the candidate from the list of terms and decrement the occurrences of other terms.
                  newTermOccs = M.mapWithKey (\term (occs, legendOccs) -> (occs, countProperSubterms term candidate : legendOccs))
                                $ M.delete candidate termOccs
                  newAbbrevs = M.insert candidate abbrevName abbrevs
              in
                go newTermOccs newPrefixMap newAbbrevs
              
            
    -- | Collect all terms in our graph along with their number of occurrences
    allTermOccs :: M.Map LNTerm (Int, [Int])
    allTermOccs = 
      let terms = concatMap getNodeTerms (get grNodes repr) ++ concatMap (\c -> concatMap getNodeTerms $ get cNodes c) (get grClusters repr) in
      M.map (\occs -> (occs, [])) $ M.fromListWith (+) $ map (\t -> (t,1)) terms

    -- | Collect all terms in a single graph node. 
    -- At the moment terms only appear in SystemNodes and UnsolvedActionNodes.
    getNodeTerms :: Node -> [LNTerm]
    getNodeTerms (Node _ (SystemNode ru)) =
      concatMap getFactTerms (get rPrems ru)
      ++ concatMap getFactTerms (get rActs ru)
      ++ concatMap getFactTerms (get rConcs ru) 
    getNodeTerms (Node _ (UnsolvedActionNode facts)) = concatMap getFactTerms facts
    getNodeTerms _ = []

    -- | Collect all terms of a LNFact.
    -- We filter out pairs so that we do not abbreviate pairs of terms but only the inner terms.
    getFactTerms :: LNFact -> [LNTerm]
    getFactTerms fact = filter (not . isPair) $ concatMap getSubTerms $ factTerms fact 

    -- | Subterms are the term itself along with ts of an FApp
    getSubTerms :: LNTerm -> [LNTerm]
    getSubTerms t@(viewTerm -> FApp _ ts) = t : ts
    getSubTerms t = [t]

    -- | Collect all names that appear somewhere in the graph to avoid generating abbreviations with the same name as existing objects.
    --  quickest way to do this is to render the entire graph as a string and pull out all alphanumeric substrings.
    --  We convert all names to upper-case to compare in a case-insensitive way.
    allNames :: [String]
    allNames = 
      let rendered = T.pack $ show repr
          names = filter (not . null) $ map (T.unpack . T.toUpper) $ T.split (not . isAlphaNum) rendered
      in
        sort $ nub names

    -- | For a number of weighted terms, take the first aoMaxAbbrevs terms sorted by decreasing weight.
    filterCandidateTerm :: [(LNTerm, Weight)] -> Maybe (LNTerm, Weight)
    filterCandidateTerm weightedTerms = 
      let relevantWeights = sortOn (Data.Ord.Down . snd) $ filter (\(_, weight) -> weight > 0) weightedTerms in
      listToMaybe relevantWeights

    -- | For a given list of terms, find suitable abbreviations and return a mapping from the original to the abbreviated terms. 
    -- The prefix index map is initially empty and accumulates the next possible index candidate for each prefix while we create abbreviations.
    abbreviateTerms :: [LNTerm] -> [(LNTerm, LNTerm)]
    abbreviateTerms ts =
      let (_, abbrevNames) = mapAccumL (abbreviateTerm options allNames) M.empty ts in
      zip ts abbrevNames

    -- | For a given list of (expansion, abbrevName) pairs, compute a recursiveExpansion that is the original expansion term where any subterm which is also an expansion is replaced by the respective abbrevName. 
    -- Going through all expansions once is enough because abbrevNames do not contain any subterms themselves, so we do not introduce any new possibilities for recursive occurrences. 
    --
    -- ==== __Example__:
    -- [(A(B, C), H1), (B, H2)] => [(A(H2, C), H1), (B, H2)]
    makeRecursive :: [(LNTerm, LNTerm)] -> Abbreviations
    makeRecursive abbrevs = 
      let replacementMap = M.fromList abbrevs 
          replacement t = fromMaybe t (M.lookup t replacementMap)
          recursiveExpansions = map (replaceProperSubterm replacement . fst) abbrevs
          recursiveAbbrevs = zipWith (\(expansion, abbrevName) recursiveExpansion -> 
                                        (expansion, (abbrevName, recursiveExpansion))) 
                                      abbrevs recursiveExpansions
      in
        M.fromList recursiveAbbrevs

-- | Go through an LNTerm and replace all possible subterms with their abbreviation top-down.
applyAbbreviationsTerm :: (LNTerm -> Maybe AbbreviationTerm) -> LNTerm -> LNTerm
applyAbbreviationsTerm lookupTerm term = 
  let replaceWithAbbrev t = fromMaybe t $ lookupTerm t
      replacedTerm = replaceSubterm replaceWithAbbrev term
  in
    replacedTerm

-- | Go through an LNFact and apply the abbreviations to all contained LNTerm's.
applyAbbreviationsFact :: (LNTerm -> Maybe AbbreviationTerm) -> LNFact -> LNFact
applyAbbreviationsFact lookupTerm fact = 
  let terms = factTerms fact
      replacedTerms = map (applyAbbreviationsTerm lookupTerm) terms
  in 
    fact { factTerms = replacedTerms }
