{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE ViewPatterns #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- s implements generating abbreviations for a given graph representation.
-- hlsearch
--  abbreviation are computed from all LNTerm's in the graph and the method is based on cleandot.py 
-- All terms in the graph are weighted based on their multiplicity and length, highest weighted terms are abbreviated first.
--  abbreviation itself is based on the string representation of a term. 
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
-- | Options to control the abbreviation generation.
data AbbreviationOptions = AbbreviationOptions 
  { aoMaxAbbrevs :: Int   -- ^ The maximum number of abbreviations to generate.
  , aoFirstIndex :: Int   -- ^ The first index to use when generating abbreviations.
  , aoPrefixLength :: Int -- ^ The length of an abbreviation prefixes.
  }
  deriving( Eq, Ord )

-- | The default abbreviation options.
defaultAbbreviationOptions :: AbbreviationOptions
defaultAbbreviationOptions = AbbreviationOptions 
  { aoMaxAbbrevs = 10
  , aoFirstIndex = 1
  , aoPrefixLength = 2
  }

-- | Lookup a single term in an abbreviations map and return the abbreviation name.
lookupAbbreviation :: LNTerm -> Abbreviations -> Maybe AbbreviationTerm
lookupAbbreviation t abbrevs = fst <$> M.lookup t abbrevs

-- | Weigh each term based on its size and how often it appears in the graph.
judgeTerm :: LNTerm -> Int -> Float
judgeTerm t occs 
  | termSize < 7 = -1.0
  | (termSize < 20) && occs == 1 = -1.0
  | otherwise = (fromIntegral (2 + occs) ^ (2 :: Integer)) * fromIntegral termSize
  where
    -- | The termsize is the length of the term rendered as a string.
    termSize :: Int
    termSize = length $ render $ prettyLNTerm t

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
computeAbbreviations :: GraphRepr -> AbbreviationOptions -> Abbreviations 
computeAbbreviations repr options = 
  let allTermOccs = getAllTermOccs repr
      allWeightedTerms = M.mapWithKey judgeTerm allTermOccs
      toAbbreviate = filterWeights $ M.toList allWeightedTerms
      abbrevs = abbreviateTerms toAbbreviate
      recursiveAbbrevs = makeRecursive abbrevs
  in 
    recursiveAbbrevs
  where
    -- | Collect all terms in our graph along with their number of occurrences
    getAllTermOccs :: GraphRepr -> M.Map LNTerm Int
    getAllTermOccs (clusters, nodes, _) = 
      let terms = concatMap getNodeTerms nodes ++ concatMap (\c -> concatMap getNodeTerms $ get cNodes c) clusters in
      M.fromListWith (+) $ map (\t -> (t,1)) terms

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
    filterWeights :: [(LNTerm, Float)] -> [LNTerm]
    filterWeights weightedTerms = take (aoMaxAbbrevs options) $ mapMaybe removeNegativeWeights $ sortOn (Data.Ord.Down . snd) weightedTerms

    -- | Terms with negative weights should never be abbreviated.
    removeNegativeWeights (t, w)
      | w < 0.0 = Nothing
      | otherwise = Just t

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
applyAbbreviationsTerm :: Abbreviations -> LNTerm -> LNTerm
applyAbbreviationsTerm abbrevs term = 
  let replaceWithAbbrev t = fromMaybe t $ lookupAbbreviation t abbrevs
      replacedTerm = replaceSubterm replaceWithAbbrev term
  in
    replacedTerm

-- | Go through an LNFact and apply the abbreviations to all contained LNTerm's.
applyAbbreviationsFact :: Abbreviations -> LNFact -> LNFact
applyAbbreviationsFact abbrevs fact = 
  let terms = factTerms fact
      replacedTerms = map (applyAbbreviationsTerm abbrevs) terms
  in 
    fact { factTerms = replacedTerms }
