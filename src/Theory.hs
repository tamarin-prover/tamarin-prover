{-# LANGUAGE TemplateHaskell, TupleSections, DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving, TypeSynonymInstances, FlexibleInstances #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Theory datatype and transformations on it.
module Theory (
  -- * Lemmas
    LemmaAttribute(..)
  , Lemma(..)
  , lName
  , lFormulaE
  , lFormulaAC
  , lAttributes
  , lProof
  , unprovenLemma 
  , skeletonLemma

  -- * Theories
  , Theory(..)
  , TheoryItem(..)
  , thyName
  , thySignature
  , thyCache
  , thyItems
  , addLemma
  , removeLemma
  , lookupLemma
  , addComment
  , addStringComment
  , addFormalComment
  , cprRuleE

  -- ** Open theories
  , OpenTheory
  , defaultOpenTheory
  , addProtoRule
  , addIntrRuleACs
  , applyPartialEvaluation

  -- ** Closed theories
  , ClosedTheory
  , ClosedRuleCache(..) -- FIXME: this is only exported for the Binary instances
  , closeTheory
  , openTheory

  , ClosedProtoRule(..)

  , getLemmas
  , getIntrVariants
  , getProtoRuleEs
  , getProofContext
  , getClassifiedRules

  , getCaseDistinction

  -- ** Proving
  , ProofSkeleton
  , proveTheory
  , applicableProofMethods

  -- ** Lemma references
  , lookupLemmaProof
  , modifyLemmaProof

  -- * Pretty printing
  , prettyFormalComment
  , prettyLemmaName
  , prettyLemma
  , prettyClosedTheory
  , prettyOpenTheory

  , prettyClosedSummary

  , prettyIntruderVariants

  -- * Convenience exports
  , module Theory.Proof
  , module Theory.IntruderRules
  
  ) where

import           Prelude hiding ( (.), id )
                 
import           Data.Maybe
import           Data.Monoid (Sum(..))
import qualified Data.Set as S
import           Data.List
import           Data.Foldable (Foldable, foldMap)
import           Data.Traversable (Traversable, traverse)
import           Data.DeriveTH
import           Data.Binary
                 
import           Control.Basics
import           Control.Parallel.Strategies
import           Control.DeepSeq
import           Control.Category
import qualified Control.Monad.State     as MS
import           Control.Monad.Reader

import qualified Extension.Data.Label    as L
import           Extension.Data.Label    hiding (get)

import           Text.Isar
                 
import           Theory.Pretty
import           Theory.Rule
import           Theory.RuleSet
import           Theory.RuleVariants
import           Theory.IntruderRules
import           Theory.Proof
import           Theory.AbstractInterpretation


------------------------------------------------------------------------------
-- To MOVE
------------------------------------------------------------------------------

-- | Vertically separate a list of documents by empty lines.
vsep :: Document d => [d] -> d
vsep = foldr ($--$) emptyDoc


------------------------------------------------------------------------------
-- Specific proof types
------------------------------------------------------------------------------

-- | Proof skeletons are used to represent proofs in open theories.
type ProofSkeleton    = Proof ()

-- | Convert a proof skeleton to an incremental proof without any sequent
-- annotations.
skeletonToIncrementalProof :: ProofSkeleton -> IncrementalProof
skeletonToIncrementalProof = fmap (fmap (const Nothing))

-- | Convert an incremental proof to a proof skeleton by dropping all
-- annotations.
incrementalToSkeletonProof :: IncrementalProof -> ProofSkeleton
incrementalToSkeletonProof = fmap (fmap (const ()))


------------------------------------------------------------------------------
-- Commented sets of rewriting rules
------------------------------------------------------------------------------

-- | A protocol rewriting rule modulo E together with its possible assertion
-- soundness proof.
type OpenProtoRule = ProtoRuleE

-- | A closed proto rule lists its original rule modulo E, the corresponding
-- variant modulo AC, and if required the assertion soundness proof.
data ClosedProtoRule = ClosedProtoRule 
       { _cprRuleE  :: ProtoRuleE             -- original rule modulo E
       , _cprRuleAC :: ProtoRuleAC            -- variant modulo AC
       }
       deriving( Eq, Ord, Show )

type OpenRuleCache = [IntrRuleAC]

data ClosedRuleCache = ClosedRuleCache
       { _crcRules            :: ClassifiedRules
       , _crcUntypedCaseDists :: [CaseDistinction]
       , _crcTypedCaseDists   :: [CaseDistinction]
       }
       deriving( Eq, Ord, Show )


$(mkLabels [''ClosedProtoRule, ''ClosedRuleCache])

instance HasRuleName ClosedProtoRule where
    ruleName = ruleName . L.get cprRuleE


-- Relation between open and closed rule sets
---------------------------------------------

-- | All intruder rules of a set of classified rules.
intruderRules :: ClassifiedRules -> [IntrRuleAC]
intruderRules rules = do
    Rule (IntrInfo i) ps cs as <- joinAllRules rules
    return $ Rule i ps cs as

-- | Open a rule cache. Variants and precomputed case distinctions are dropped.
openRuleCache :: ClosedRuleCache -> OpenRuleCache
openRuleCache = intruderRules . L.get crcRules

-- | Open a protocol rule; i.e., drop variants and proof annotations.
openProtoRule :: ClosedProtoRule -> OpenProtoRule
openProtoRule = L.get cprRuleE

-- | Close a protocol rule; i.e., compute AC variant and typing assertion
-- soundness sequent, if required.
closeProtoRule :: MaudeHandle -> OpenProtoRule -> ClosedProtoRule
closeProtoRule hnd ruE = ClosedProtoRule ruE (variantsProtoRule hnd ruE)

-- | Close a rule cache. Hower, note that the
-- requires case distinctions are not computed here.
closeRuleCache :: [LNGuarded]        -- ^ Typing lemmas.
               -> SignatureWithMaude -- ^ Signature of theory.
               -> [ClosedProtoRule]  -- ^ Protocol rules with variants.
               -> OpenRuleCache      -- ^ Intruder rules modulo AC.
               -> ClosedRuleCache    -- ^ Cached rules and case distinctions.
closeRuleCache typingAsms sig protoRules intrRulesAC = 
    ClosedRuleCache classifiedRules untypedCaseDists typedCaseDists
  where
    ctxt0 = ProofContext sig classifiedRules UntypedCaseDist [] False {- No induction -}
    -- precomputing the case distinctions
    untypedCaseDists = precomputeCaseDistinctions ctxt0 [] 
    typedCaseDists   = 
        refineWithTypingAsms typingAsms ctxt0 untypedCaseDists

    -- classifying the rules
    rulesAC = (fmap IntrInfo                      <$> intrRulesAC) <|> 
              ((fmap ProtoInfo . L.get cprRuleAC) <$> protoRules)

    anyOf ps = partition (\x -> any ($ x) ps)

    (nonProto, proto) = anyOf [isDestrRule, isConstrRule] rulesAC
    (constr, destr)   = anyOf [isConstrRule] nonProto

    -- and sort them into ClassifiedRules datastructure for later use in proofs
    classifiedRules = ClassifiedRules
      { _crConstruct  = constr
      , _crDestruct   = destr
      , _crProtocol   = proto
      }



------------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------------

data LemmaAttribute = 
         TypingLemma
       | ReuseLemma
       | InvariantLemma
       deriving( Eq, Ord, Show )

-- | A lemma describes a property that holds in the context of a theory
-- together with a proof of its correctness.
data Lemma p = Lemma
       { _lName       :: String
       , _lFormulaE   :: FormulaE
       , _lFormulaAC  :: Maybe FormulaAC
       , _lAttributes :: [LemmaAttribute]
       , _lProof      :: p
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''Lemma])


-- Instances
------------

instance Functor Lemma where
    fmap f (Lemma n fE fAC atts prf) = Lemma n fE fAC atts (f prf)

instance Foldable Lemma where
    foldMap f = f . L.get lProof

instance Traversable Lemma where
    traverse f (Lemma n fE fAC atts prf) = Lemma n fE fAC atts <$> f prf


-- Lemma construction/modification
----------------------------------

-- | Create a new unproven lemma from a formula modulo E.
unprovenLemma :: String -> [LemmaAttribute] -> FormulaE -> Lemma ProofSkeleton
unprovenLemma name atts fmE = Lemma name fmE Nothing atts (unproven ())

skeletonLemma :: String -> [LemmaAttribute] -> FormulaE
              -> ProofSkeleton -> Lemma ProofSkeleton
skeletonLemma name atts fmE = Lemma name fmE Nothing atts

-- | The case-distinction kind allowed for a lemma
lemmaCaseDistKind :: Lemma p -> CaseDistKind
lemmaCaseDistKind lem
  | TypingLemma `elem` L.get lAttributes lem = UntypedCaseDist
  | otherwise                                = TypedCaseDist
   

------------------------------------------------------------------------------
-- Theories
------------------------------------------------------------------------------

-- | A formal comment is a header together with the body of the comment.
type FormalComment = (String, String)

-- | A theory item built over the given rule type.
data TheoryItem r p = 
       RuleItem r
     | LemmaItem (Lemma p)
     | TextItem FormalComment
     deriving( Show, Eq, Ord, Functor )


-- | A theory contains a single set of rewriting rules modeling a protocol
-- and the lemmas that 
data Theory sig c r p = Theory {
         _thyName      :: String
       , _thySignature :: sig
       , _thyCache     :: c
       , _thyItems     :: [TheoryItem r p]
       }

$(mkLabels [''Theory])

-- | Open theories can be extended. Invariants:
--   1. Lemma names are unique. 
type OpenTheory = 
    Theory SignaturePure [IntrRuleAC] OpenProtoRule ProofSkeleton 

deriving instance Show OpenTheory

-- | Closed theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedTheory = 
    Theory SignatureWithMaude ClosedRuleCache ClosedProtoRule IncrementalProof

deriving instance Show ClosedTheory


-- Shared theory modification functions
---------------------------------------

-- | Fold a theory item.
foldTheoryItem :: (r -> a) -> (Lemma p -> a) -> (FormalComment -> a) 
               -> TheoryItem r p -> a
foldTheoryItem fRule fLemma fText i = case i of
    RuleItem r  -> fRule r
    LemmaItem l -> fLemma l
    TextItem t  -> fText t

-- | Map a theory item.
mapTheoryItem :: (r -> r') -> (p -> p') -> TheoryItem r p -> TheoryItem r' p'
mapTheoryItem f g = foldTheoryItem (RuleItem . f) (LemmaItem . fmap g) TextItem

-- | All rules of a theory.
theoryRules :: Theory sig c r p -> [r]
theoryRules = foldTheoryItem return (const []) (const []) <=< L.get thyItems

-- | All lemmas of a theory.
theoryLemmas :: Theory sig c r p -> [Lemma p]
theoryLemmas = foldTheoryItem (const []) return (const []) <=< L.get thyItems

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addLemma :: Lemma p -> Theory sig c r p -> Maybe (Theory sig c r p)
addLemma l thy = do
    guard (isNothing $ lookupLemma (L.get lName l) thy)
    return $ modify thyItems (++ [LemmaItem l]) thy

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemma :: String -> Theory sig c r p -> Maybe (Theory sig c r p)
removeLemma lemmaName thy = do
    _ <- lookupLemma lemmaName thy
    return $ modify thyItems (concatMap fItem) thy
  where
    fItem   = foldTheoryItem (return . RuleItem) check (return . TextItem)
    check l = do guard (L.get lName l /= lemmaName); return (LemmaItem l)

-- | Find the lemma with the given name.
lookupLemma :: String -> Theory sig c r p -> Maybe (Lemma p)
lookupLemma name = find ((name ==) . L.get lName) . theoryLemmas

-- | Add a comment to the theory.
addComment :: Doc -> Theory sig c r p -> Theory sig c r p
addComment c = modify thyItems (++ [TextItem ("", render c)]) 

-- | Add a comment represented as a string to the theory.
addStringComment :: String -> Theory sig c r p -> Theory sig c r p
addStringComment = addComment . vcat . map text . lines

addFormalComment :: FormalComment -> Theory sig c r p -> Theory sig c r p
addFormalComment c = modify thyItems (++ [TextItem c]) 


------------------------------------------------------------------------------
-- Open theory construction / modification
------------------------------------------------------------------------------

-- | Default theory
defaultOpenTheory :: OpenTheory
defaultOpenTheory = Theory "default" emptySignaturePure [] []

-- | Open a theory by dropping the closed world assumption and values whose
-- soundness dependens on it.
openTheory :: ClosedTheory -> OpenTheory
openTheory  (Theory n sig c items) = 
    Theory n (toSignaturePure sig) (openRuleCache c) 
      (map (mapTheoryItem openProtoRule incrementalToSkeletonProof) items)

-- | Find the open protocol rule with the given name.
lookupOpenProtoRule :: ProtoRuleName -> OpenTheory -> Maybe OpenProtoRule
lookupOpenProtoRule name = 
    find ((name ==) . L.get rInfo) . theoryRules

-- | Add a new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addProtoRule :: ProtoRuleE -> OpenTheory -> Maybe OpenTheory
addProtoRule ruE thy = do
    guard (maybe True ((ruE ==)) $ 
        lookupOpenProtoRule (L.get rInfo ruE) thy)
    return $ modify thyItems (++ [RuleItem ruE]) thy

-- | Add intruder proof rules.
addIntrRuleACs :: [IntrRuleAC] -> OpenTheory -> OpenTheory
addIntrRuleACs rs' = modify (thyCache) (\rs -> nub $ rs ++ rs')


------------------------------------------------------------------------------
-- Closed theory querying / construction / modification
------------------------------------------------------------------------------

-- querying
-----------

-- | All lemmas.
getLemmas :: ClosedTheory -> [Lemma IncrementalProof]
getLemmas = theoryLemmas

-- | The variants of the intruder rules.
getIntrVariants :: ClosedTheory -> [IntrRuleAC]
getIntrVariants = intruderRules . L.get (crcRules . thyCache)

-- | All protocol rules modulo E.
getProtoRuleEs :: ClosedTheory -> [ProtoRuleE]
getProtoRuleEs = map openProtoRule . theoryRules 

-- | Get the proof context for a lemma of the closed theory.
getProofContext :: Lemma a -> ClosedTheory -> ProofContext
getProofContext l thy = ProofContext
    ( L.get thySignature          thy)
    ( L.get (crcRules . thyCache) thy)
    kind
    ( L.get (cases . thyCache)    thy)
    useIndu
  where
    kind    = lemmaCaseDistKind l
    useIndu = any (`elem` [TypingLemma, InvariantLemma]) (L.get lAttributes l)
    cases   = case kind of UntypedCaseDist -> crcUntypedCaseDists
                           TypedCaseDist   -> crcTypedCaseDists

-- | The classified set of rules modulo AC in this theory.
getClassifiedRules :: ClosedTheory -> ClassifiedRules
getClassifiedRules = L.get (crcRules . thyCache)

-- | The precomputed case distinctions.
getCaseDistinction :: CaseDistKind -> ClosedTheory -> [CaseDistinction]
getCaseDistinction UntypedCaseDist = L.get (crcUntypedCaseDists . thyCache)
getCaseDistinction TypedCaseDist   = L.get (crcTypedCaseDists . thyCache)


-- construction
---------------

-- | Close a theory by closing its associated rule set and converting the proof
-- skeletons to unannotated incremental proofs and caching AC variants as well
-- as precomputed case distinctions.
-- 
-- This function initializes the relation to the Maude process with the
-- correct signature. This is the right place to do that because in a closed 
-- theory the signature may not change any longer.
closeTheory :: FilePath         -- ^ Path to the Maude executable.
            -> OpenTheory
            -> IO ClosedTheory
closeTheory maudePath thy0 = do
    sig <- toSignatureWithMaude maudePath $ L.get thySignature thy0
    return $ closeTheoryWithMaude sig thy0

-- | Close a theory given a maude signature. This signature must be valid for
-- the given theory.
closeTheoryWithMaude :: SignatureWithMaude -> OpenTheory -> ClosedTheory
closeTheoryWithMaude sig thy0 = do
    proveTheory addSorrys $ Theory (L.get thyName thy0) sig cache items
  where
    cache     = closeRuleCache typAsms sig rules $ L.get thyCache thy0
    addSorrys = checkAndExtendProver (sorryProver "not yet proven")

    -- Maude / Signature handle
    hnd = L.get sigmMaudeHandle sig

    -- close all theory items: in parallel
    (items, _solveRel, _breakers) = (`runReader` hnd) $ addSolvingLoopBreakers
       ((closeTheoryItem <$> L.get thyItems thy0) `using` parList rdeepseq)
    closeTheoryItem = foldTheoryItem 
       (RuleItem . closeProtoRule hnd) 
       (LemmaItem . ensureFormulaAC . fmap skeletonToIncrementalProof)
       TextItem

    -- extract typing lemmas
    typAsms = do 
        LemmaItem lem <- items
        guard (TypingLemma `elem` L.get lAttributes lem)
        let toGuarded = fmap negateGuarded . fromFormulaNegate
        case toGuarded <$> L.get lFormulaAC lem of
          Just (Right gf) -> return gf
          Just (Left err) -> error $ "closeTheory: " ++ err
          _               -> mzero

    -- extract protocol rules
    rules = theoryRules (Theory errClose errClose errClose items)
    errClose = error "closeTheory"

    addSolvingLoopBreakers = useAutoLoopBreakersAC
        (liftToItem $ enumPrems . L.get cprRuleAC)
        (liftToItem $ enumConcs . L.get cprRuleAC)
        (liftToItem $ getDisj . L.get (pracVariants . rInfo . cprRuleAC))
        addBreakers
      where
        liftToItem f (RuleItem ru) = f ru
        liftToItem _ _             = []

        addBreakers bs (RuleItem ru) = 
            RuleItem (L.set (pracLoopBreakers . rInfo . cprRuleAC) bs ru)
        addBreakers _  item = item




-- Partial evaluation / abstract interpretation
-----------------------------------------------

-- | Apply partial evaluation.
applyPartialEvaluation :: EvaluationStyle -> ClosedTheory -> ClosedTheory
applyPartialEvaluation evalStyle thy0 =
    closeTheoryWithMaude sig $
    L.modify thyItems replaceProtoRules (openTheory thy0)
  where
    sig          = L.get thySignature thy0
    ruEs         = getProtoRuleEs thy0
    (st', ruEs') = (`runReader` L.get sigmMaudeHandle sig) $ 
                   partialEvaluation evalStyle ruEs

    replaceProtoRules [] = []
    replaceProtoRules (item:items)
      | isRuleItem item  = 
          [ TextItem ("text", render ppAbsState)
              
          ] ++ map RuleItem ruEs' ++ filter (not . isRuleItem) items
      | otherwise        = item : replaceProtoRules items

    isRuleItem (RuleItem _) = True
    isRuleItem _            = False

    ppAbsState = 
      (text $ " the abstract state after partial evaluation" 
              ++ " contains " ++ show (S.size st') ++ " facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList st') $--$
      (text $ "This abstract state results in " ++ show (length ruEs') ++ 
              " refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (length ruEs) ++ ".\n\n")

-- Applying provers
-------------------

-- | A list of proof methods that could be applied to the given sequent.
applicableProofMethods :: ProofContext -> Sequent -> [ProofMethod]
applicableProofMethods ctxt se = do
    m <- possibleProofMethods ctxt se
    guard (isJust $ execProofMethod ctxt m se)
    return m

-- | Prove both the assertion soundness as well as all lemmas of the theory. If
-- the prover fails on a lemma, then its proof remains unchanged.
proveTheory :: Prover -> ClosedTheory -> ClosedTheory
proveTheory prover thy = 
    modify thyItems ((`MS.evalState` []) . mapM prove) thy
  where
    prove item = case item of
      LemmaItem l0 -> do l <- MS.gets (LemmaItem . proveLemma l0)
                         MS.modify (l :)
                         return l
      _            -> do return item

    proveLemma l0 preItems =
        modify lProof add l
      where
        l       = ensureFormulaAC l0
        ctxt    = getProofContext l thy 
        se      = formulaToSequent ctxt preItems $ fromJust $ L.get lFormulaAC l
        add prf = fromMaybe prf $ runProver prover ctxt se prf

-- | Convert a formula modulo AC to a sequent.
formulaToSequent :: ProofContext -> [TheoryItem r p] -> FormulaAC -> Sequent
formulaToSequent ctxt lems = 
    addLemmasToSequent lems . sequentFromFormula (L.get pcCaseDistKind ctxt)

-- | Add the lemmas that have an associated AC variant to this sequent.
addLemmasToSequent :: [TheoryItem r p] -> Sequent -> Sequent
addLemmasToSequent items se = 
    modify sLemmas (S.union gfs) se 
  where
    gfs = S.fromList $ gatherReusableLemmas (L.get sCaseDistKind se) items

-- | Gather reusable lemmas to be added to a sequent.
gatherReusableLemmas :: CaseDistKind -> [TheoryItem r p] -> [LNGuarded]
gatherReusableLemmas kind items = do
    LemmaItem lem <- items
    guard $ lemmaCaseDistKind lem <= kind && 
            ReuseLemma `elem` L.get lAttributes lem
    Just (Right gf) <- [fromFormula <$> L.get lFormulaAC lem]
    return gf

-- | Ensure that the AC variant of a formula is present.
ensureFormulaAC :: Lemma p -> Lemma p
ensureFormulaAC l =
    set lFormulaAC (Just fmAC) l
  where
    -- FIXME: AC-variant of formula is formula itself.
    --        This is ensured by well-formed check (not implemented yet).
    fmAC = fromMaybe (L.get lFormulaE l) $ L.get lFormulaAC l


------------------------------------------------------------------------------
-- References to lemmas
------------------------------------------------------------------------------

-- | Lemmas are referenced by their name.
type LemmaRef = String

-- | Resolve a path in a theory. 
lookupLemmaProof :: LemmaRef -> ClosedTheory -> Maybe IncrementalProof
lookupLemmaProof name thy = L.get lProof <$> lookupLemma name thy

-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProof :: Prover -> LemmaRef -> ClosedTheory -> Maybe ClosedTheory
modifyLemmaProof prover name thy = 
    modA thyItems changeItems thy
  where
    findLemma (LemmaItem lem) = name == L.get lName lem
    findLemma _               = False

    change preItems (LemmaItem l0) = do
         let l1   = ensureFormulaAC l0
             ctxt = getProofContext l1 thy
         se <- formulaToSequent ctxt preItems <$> L.get lFormulaAC l1
         l2 <- modA lProof (runProver prover ctxt se) l1
         return $ LemmaItem l2
    change _ _ = error "LemmaProof: change: impossible"

    changeItems items = case break findLemma items of
        (pre, i:post) -> do
             i' <- change pre i
             return $ pre ++ i':post
        (_, []) -> Nothing


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print a formal comment
prettyFormalComment :: HighlightDocument d => String -> String -> d
prettyFormalComment "" body = multiComment_ [body]
prettyFormalComment header body = text $ header ++ "{*" ++ body ++ "*}"

-- | Pretty print a theory.
prettyTheory :: HighlightDocument d 
             => (sig -> d) -> (c -> d) -> (r -> d) -> (p -> d)
             -> Theory sig c r p -> d
prettyTheory ppSig ppCache ppRule ppPrf thy = vsep $
    [ kwTheoryHeader $ L.get thyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get thySignature thy
    , ppCache $ L.get thyCache thy 
    ] ++
    parMap rdeepseq ppItem (L.get thyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldTheoryItem 
        ppRule (prettyLemma ppPrf) (\(h,c) -> prettyFormalComment h c)

-- | Pretty print the lemma name together with its attributes.
prettyLemmaName :: HighlightDocument d => Lemma p -> d
prettyLemmaName l = case L.get lAttributes l of
      [] -> text (L.get lName l)
      as -> text (L.get lName l) <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)
  where
    prettyLemmaAttribute TypingLemma    = text "typing"
    prettyLemmaAttribute ReuseLemma     = text "reuse"
    prettyLemmaAttribute InvariantLemma = text "invariant"

-- | Pretty print a lemma.
prettyLemma :: HighlightDocument d => (p -> d) -> Lemma p -> d
prettyLemma ppPrf l =
    kwLemmaModulo "E" <-> prettyLemmaName l <> colon $-$ 
    (nest 2 $ doubleQuotes $ prettyFormulaE $ L.get lFormulaE l)
    $-$
    maybe emptyDoc ppFormulaAC (L.get lFormulaAC l)
    $-$
    maybe emptyDoc ppFormulaACGuarded (L.get lFormulaAC l)
    -- $-$
    -- maybe emptyDoc ppFormulaACInduction (L.get lFormulaAC l)
    $-$
    ppPrf (L.get lProof l)
  where
    ppFormulaAC fmAC
      | fmAC == L.get lFormulaE l = multiComment_ ["proof based on the same lemma modulo AC"]
      | otherwise               =
          multiComment
              ( text "proof based on the following equivalent lemma modulo AC:" $-$
                doubleQuotes (prettyFormulaAC fmAC) )

    ppFormulaACGuarded fmAC = case fromFormulaNegate fmAC of
        Left err -> multiComment_ 
            ["conversion to doubly-guarded formula failed:", err]
        Right gf -> multiComment
            ( text "guarded formula characterizing all attacks:" $-$
              doubleQuotes (prettyGuarded gf) )

    {-
    ppFormulaACInduction fmAC = case fmInd of
        Left err -> multiComment_ 
            ["formula cannot be proven by induction:", err]
        Right gf -> multiComment
            ( text "proof by induction possible over the formula:" $-$
              doubleQuotes (prettyGuarded gf) )
      where
        fmInd = applyInduction =<< fromFormulaNegate fmAC
    -}

-- | Pretty-print a non-empty bunch of intruder rules.
prettyIntruderVariants :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntruderVariants vs = vcat . intersperse (text "") $ map prettyIntrRuleAC vs

{-
-- | Pretty-print the intruder variants section.
prettyIntrVariantsSection :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntrVariantsSection rules = 
    prettyFormalComment "section" " Finite Variants of the Intruder Rules " $--$
    nest 1 (prettyIntruderVariants rules)
-}

-- | Pretty print an open rule together with its assertion soundness proof.
prettyOpenProtoRule :: HighlightDocument d => OpenProtoRule -> d
prettyOpenProtoRule = prettyProtoRuleE

prettyIncrementalProof :: HighlightDocument d => IncrementalProof -> d
prettyIncrementalProof = prettyProofWith ppStep (const id)
  where
    ppStep step =
       (if isNothing (psInfo step) then text "!" else emptyDoc) <-> 
       prettyProofMethod (psMethod step)

-- | Pretty print an closed rule together with its assertion soundness proof.
prettyClosedProtoRule :: HighlightDocument d => ClosedProtoRule -> d
prettyClosedProtoRule cru =
    (prettyProtoRuleE  $ L.get cprRuleE cru) $--$
    (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$ ppRuleAC)
  where
    ruAC = L.get cprRuleAC cru
    ppRuleAC
      | isTrivialProtoRuleAC ruAC = multiComment_ ["has exactly the trivial AC variant"]
      | otherwise                 = multiComment $ prettyProtoRuleAC ruAC

-- | Pretty print an open theory.
prettyOpenTheory :: HighlightDocument d => OpenTheory -> d
prettyOpenTheory = 
    prettyTheory prettySignaturePure
                 (const emptyDoc) prettyOpenProtoRule prettyProof
                 -- prettyIntrVariantsSection prettyOpenProtoRule prettyProof

-- | Pretty print a closed theory.
prettyClosedTheory :: HighlightDocument d => ClosedTheory -> d
prettyClosedTheory thy = 
    prettyTheory prettySignatureWithMaude
                 (const emptyDoc)
                 -- (prettyIntrVariantsSection . intruderRules . L.get crcRules) 
                 prettyClosedProtoRule
                 prettyIncrementalProof
                 thy
    -- $--$
    -- (multiComment $ 
      -- let ruEs = getProtoRuleEs thy
      -- in prettyAbstractState ruEs $ absInterpretation ruEs
    -- )

prettyClosedSummary :: Document d => ClosedTheory -> d
prettyClosedSummary thy =
    vcat lemmaSummaries
  where
    lemmaSummaries = do
        LemmaItem lem  <- L.get thyItems thy
        let (status, Sum siz) = foldProof proofStepSummary $ L.get lProof lem
        return $ text (L.get lName lem) <> colon <-> 
                 text (showProofStatus status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))

-- Instances: FIXME: Sort them into the right files
--------------------------------------------------

$( derive makeBinary ''TheoryItem)
$( derive makeBinary ''LemmaAttribute)
$( derive makeBinary ''Lemma)
$( derive makeBinary ''ClosedProtoRule)
$( derive makeBinary ''ClosedRuleCache)
$( derive makeBinary ''Theory)

$( derive makeNFData ''TheoryItem)
$( derive makeNFData ''LemmaAttribute)
$( derive makeNFData ''Lemma)
$( derive makeNFData ''ClosedProtoRule)
$( derive makeNFData ''ClosedRuleCache)
$( derive makeNFData ''Theory)

