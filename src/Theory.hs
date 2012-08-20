{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Theory datatype and transformations on it.
module Theory (
  -- * Axioms
    Axiom(..)
  , axName
  , axFormula

  -- * Lemmas
  , LemmaAttribute(..)
  , TraceQuantifier(..)
  , Lemma
  , lName
  , lTraceQuantifier
  , lFormula
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
  , theoryRules
  , theoryLemmas
  , theoryAxioms
  , addAxiom
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
  , applyPartialEvaluation
  , addIntrRuleACs
  , normalizeTheory

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
  , getInjectiveFactInsts

  , getCaseDistinction

  -- ** Proving
  , ProofSkeleton
  , proveTheory

  -- ** Lemma references
  , lookupLemmaProof
  , modifyLemmaProof

  -- * Pretty printing
  , prettyFormalComment
  , prettyLemmaName
  , prettyAxiom
  , prettyLemma
  , prettyClosedTheory
  , prettyOpenTheory

  , prettyClosedSummary

  , prettyIntruderVariants
  , prettyTraceQuantifier

  -- * Convenience exports
  , module Theory.Model
  , module Theory.Proof

  ) where

import           Prelude                             hiding (id, (.))

import           Data.Binary
import           Data.DeriveTH
import           Data.Foldable                       (Foldable, foldMap)
import           Data.List
import           Data.Maybe
import           Data.Monoid                         (Sum(..))
import qualified Data.Set                            as S
import           Data.Traversable                    (Traversable, traverse)

import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Reader
import qualified Control.Monad.State                 as MS
import           Control.Parallel.Strategies

import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L

import           Theory.Model
import           Theory.Proof
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation
import           Theory.Tools.InjectiveFactInstances
import           Theory.Tools.LoopBreakers
import           Theory.Tools.RuleVariants

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
       , _crcInjectiveFactInsts  :: S.Set FactTag
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
closeRuleCache :: [LNGuarded]        -- ^ Axioms to use.
               -> [LNGuarded]        -- ^ Typing lemmas to use.
               -> SignatureWithMaude -- ^ Signature of theory.
               -> [ClosedProtoRule]  -- ^ Protocol rules with variants.
               -> OpenRuleCache      -- ^ Intruder rules modulo AC.
               -> ClosedRuleCache    -- ^ Cached rules and case distinctions.
closeRuleCache axioms typAsms sig protoRules intrRulesAC =
    ClosedRuleCache
        classifiedRules untypedCaseDists typedCaseDists injFactInstances
  where
    ctxt0 = ProofContext
        sig classifiedRules injFactInstances UntypedCaseDist [] AvoidInduction
        (error "closeRuleCache: trace quantifier should not matter here")

    -- inj fact instances
    injFactInstances =
        simpleInjectiveFactInstances $ L.get cprRuleE <$> protoRules

    -- precomputing the case distinctions: we make sure to only add safety
    -- axioms. Otherwise, it wouldn't be sound to use the precomputed case
    -- distinctions for properties proven using induction.
    safetyAxioms     = filter isSafetyFormula axioms
    untypedCaseDists = precomputeCaseDistinctions ctxt0 safetyAxioms
    typedCaseDists   = refineWithTypingAsms typAsms ctxt0 untypedCaseDists

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
-- Axioms (Trace filters)
------------------------------------------------------------------------------

-- | An axiom describes a property that must hold for all traces. Axioms are
-- always used as lemmas in proofs.
data Axiom = Axiom
       { _axName    :: String
       , _axFormula :: LNFormula
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''Axiom])


------------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------------

-- | An attribute for a 'Lemma'.
data LemmaAttribute =
         TypingLemma
       | ReuseLemma
       | InvariantLemma
       deriving( Eq, Ord, Show )

-- | A 'TraceQuantifier' stating whether we check satisfiability of validity.
data TraceQuantifier = ExistsTrace | AllTraces
       deriving( Eq, Ord, Show )

-- | A lemma describes a property that holds in the context of a theory
-- together with a proof of its correctness.
data Lemma p = Lemma
       { _lName            :: String
       , _lTraceQuantifier :: TraceQuantifier
       , _lFormula         :: LNFormula
       , _lAttributes      :: [LemmaAttribute]
       , _lProof           :: p
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''Lemma])


-- Instances
------------

instance Functor Lemma where
    fmap f (Lemma n qua fm atts prf) = Lemma n qua fm atts (f prf)

instance Foldable Lemma where
    foldMap f = f . L.get lProof

instance Traversable Lemma where
    traverse f (Lemma n qua fm atts prf) = Lemma n qua fm atts <$> f prf


-- Lemma queries
----------------------------------

-- | Convert a trace quantifier to a sequent trace quantifier.
toSystemTraceQuantifier :: TraceQuantifier -> SystemTraceQuantifier
toSystemTraceQuantifier AllTraces   = ExistsNoTrace
toSystemTraceQuantifier ExistsTrace = ExistsSomeTrace

-- | True iff the lemma can be used as a typing lemma.
isTypingLemma :: Lemma p -> Bool
isTypingLemma lem =
     (AllTraces == L.get lTraceQuantifier lem)
  && (TypingLemma `elem` L.get lAttributes lem)


-- Lemma construction/modification
----------------------------------

-- | Create a new unproven lemma from a formula modulo E.
unprovenLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> LNFormula
              -> Lemma ProofSkeleton
unprovenLemma name atts qua fm = Lemma name qua fm atts (unproven ())

skeletonLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> LNFormula
              -> ProofSkeleton -> Lemma ProofSkeleton
skeletonLemma name atts qua fm = Lemma name qua fm atts

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
     | AxiomItem Axiom
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
       deriving( Eq, Ord, Show )

$(mkLabels [''Theory])

-- | Open theories can be extended. Invariants:
--   1. Lemma names are unique.
type OpenTheory =
    Theory SignaturePure [IntrRuleAC] OpenProtoRule ProofSkeleton


-- | Closed theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedTheory =
    Theory SignatureWithMaude ClosedRuleCache ClosedProtoRule IncrementalProof



-- Shared theory modification functions
---------------------------------------

-- | Fold a theory item.
foldTheoryItem
    :: (r -> a) -> (Axiom -> a) -> (Lemma p -> a) -> (FormalComment -> a)
    -> TheoryItem r p -> a
foldTheoryItem fRule fAxiom fLemma fText i = case i of
    RuleItem ru   -> fRule ru
    LemmaItem lem -> fLemma lem
    TextItem txt  -> fText txt
    AxiomItem ax  -> fAxiom ax

-- | Map a theory item.
mapTheoryItem :: (r -> r') -> (p -> p') -> TheoryItem r p -> TheoryItem r' p'
mapTheoryItem f g =
    foldTheoryItem (RuleItem . f) AxiomItem (LemmaItem . fmap g) TextItem

-- | All rules of a theory.
theoryRules :: Theory sig c r p -> [r]
theoryRules =
    foldTheoryItem return (const []) (const []) (const []) <=< L.get thyItems

-- | All axioms of a theory.
theoryAxioms :: Theory sig c r p -> [Axiom]
theoryAxioms =
    foldTheoryItem (const []) return (const []) (const []) <=< L.get thyItems

-- | All lemmas of a theory.
theoryLemmas :: Theory sig c r p -> [Lemma p]
theoryLemmas =
    foldTheoryItem (const []) (const []) return (const []) <=< L.get thyItems

-- | Add a new axiom. Fails, if axiom with the same name exists.
addAxiom :: Axiom -> Theory sig c r p -> Maybe (Theory sig c r p)
addAxiom l thy = do
    guard (isNothing $ lookupAxiom (L.get axName l) thy)
    return $ modify thyItems (++ [AxiomItem l]) thy

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
    fItem   = foldTheoryItem (return . RuleItem)
                             (return . AxiomItem)
                             check
                             (return . TextItem)
    check l = do guard (L.get lName l /= lemmaName); return (LemmaItem l)

-- | Find the axiom with the given name.
lookupAxiom :: String -> Theory sig c r p -> Maybe Axiom
lookupAxiom name = find ((name ==) . L.get axName) . theoryAxioms

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

-- | Normalize the theory representation such that they remain semantically
-- equivalent. Use this function when you want to compare two theories (quite
-- strictly) for semantic equality; e.g., when testing the parser.
normalizeTheory :: OpenTheory -> OpenTheory
normalizeTheory =
    L.modify thyCache sort
  . L.modify thyItems (\items -> do
      item <- items
      return $ case item of
          LemmaItem lem ->
              LemmaItem $ L.modify lProof stripProofAnnotations $ lem
          RuleItem _    -> item
          TextItem _    -> item
          AxiomItem _   -> item)
  where
    stripProofAnnotations :: ProofSkeleton -> ProofSkeleton
    stripProofAnnotations = fmap stripProofStepAnnotations
    stripProofStepAnnotations (ProofStep method ()) =
        ProofStep (case method of
                     Sorry _         -> Sorry Nothing
                     Contradiction _ -> Contradiction Nothing
                     _               -> method)
                  ()


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
    ( L.get thySignature                    thy)
    ( L.get (crcRules . thyCache)           thy)
    ( L.get (crcInjectiveFactInsts . thyCache) thy)
    kind
    ( L.get (cases . thyCache)              thy)
    inductionHint
    (toSystemTraceQuantifier $ L.get lTraceQuantifier l)
  where
    kind    = lemmaCaseDistKind l
    cases   = case kind of UntypedCaseDist -> crcUntypedCaseDists
                           TypedCaseDist   -> crcTypedCaseDists
    inductionHint
      | any (`elem` [TypingLemma, InvariantLemma]) (L.get lAttributes l) = UseInduction
      | otherwise                                                        = AvoidInduction

-- | The facts with injective instances in this theory
getInjectiveFactInsts :: ClosedTheory -> S.Set FactTag
getInjectiveFactInsts = L.get (crcInjectiveFactInsts . thyCache)

-- | The classified set of rules modulo AC in this theory.
getClassifiedRules :: ClosedTheory -> ClassifiedRules
getClassifiedRules = L.get (crcRules . thyCache)

-- | The precomputed case distinctions.
getCaseDistinction :: CaseDistKind -> ClosedTheory -> [CaseDistinction]
getCaseDistinction UntypedCaseDist = L.get (crcUntypedCaseDists . thyCache)
getCaseDistinction TypedCaseDist   = L.get (crcTypedCaseDists . thyCache)


-- construction
---------------

-- -- | Convert a lemma to the corresponding guarded formula.
-- lemmaToGuarded :: Lemma p -> Maybe LNGuarded
-- lemmaToGuarded lem =

-- | Close a theory by closing its associated rule set and checking the proof
-- skeletons and caching AC variants as well as precomputed case distinctions.
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
    proveTheory checkProof $ Theory (L.get thyName thy0) sig cache items
  where
    cache      = closeRuleCache axioms typAsms sig rules (L.get thyCache thy0)
    checkProof = checkAndExtendProver (sorryProver Nothing)

    -- Maude / Signature handle
    hnd = L.get sigmMaudeHandle sig

    -- Close all theory items: in parallel (especially useful for variants)
    --
    -- NOTE that 'rdeepseq' is OK here, as the proof has not yet been checked
    -- and therefore no constraint systems will be unnecessarily cached.
    (items, _solveRel, _breakers) = (`runReader` hnd) $ addSolvingLoopBreakers
       ((closeTheoryItem <$> L.get thyItems thy0) `using` parList rdeepseq)
    closeTheoryItem = foldTheoryItem
       (RuleItem . closeProtoRule hnd)
       AxiomItem
       (LemmaItem . fmap skeletonToIncrementalProof)
       TextItem

    -- extract typing axioms and lemmas
    axioms  = do AxiomItem ax <- items
                 return $ formulaToGuarded_ $ L.get axFormula ax
    typAsms = do LemmaItem lem <- items
                 guard (isTypingLemma lem)
                 return $ formulaToGuarded_ $ L.get lFormula lem

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

    proveLemma lem preItems =
        modify lProof add lem
      where
        ctxt    = getProofContext lem thy
        sys     = mkSystem ctxt (theoryAxioms thy) preItems $ L.get lFormula lem
        add prf = fromMaybe prf $ runProver prover ctxt 0 sys prf

-- | Construct a constraint system for verifying the given formula.
mkSystem :: ProofContext -> [Axiom] -> [TheoryItem r p]
         -> LNFormula -> System
mkSystem ctxt axioms previousItems =
    -- Note that it is OK to add reusable lemmas directly to the system, as
    -- they do not change the considered set of traces. This is the key
    -- difference between lemmas and axioms.
    addLemmas
  . formulaToSystem (map (formulaToGuarded_ . L.get axFormula) axioms)
                    (L.get pcCaseDistKind ctxt)
                    (L.get pcTraceQuantifier ctxt)
  where
    addLemmas sys =
        insertLemmas (gatherReusableLemmas $ L.get sCaseDistKind sys) sys

    gatherReusableLemmas kind = do
        LemmaItem lem <- previousItems
        guard $    lemmaCaseDistKind lem <= kind
                && ReuseLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
        return $ formulaToGuarded_ $ L.get lFormula lem


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

    change preItems (LemmaItem lem) = do
         let ctxt = getProofContext lem thy
             sys  = mkSystem ctxt (theoryAxioms thy) preItems $ L.get lFormula lem
         lem' <- modA lProof (runProver prover ctxt 0 sys) lem
         return $ LemmaItem lem'
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
    [ kwTheoryHeader $ text $ L.get thyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get thySignature thy
    , ppCache $ L.get thyCache thy
    ] ++
    parMap rdeepseq ppItem (L.get thyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldTheoryItem
        ppRule prettyAxiom (prettyLemma ppPrf) (uncurry prettyFormalComment)

-- | Pretty print the lemma name together with its attributes.
prettyLemmaName :: HighlightDocument d => Lemma p -> d
prettyLemmaName l = case L.get lAttributes l of
      [] -> text (L.get lName l)
      as -> text (L.get lName l) <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)
  where
    prettyLemmaAttribute TypingLemma    = text "typing"
    prettyLemmaAttribute ReuseLemma     = text "reuse"
    prettyLemmaAttribute InvariantLemma = text "use_induction"

-- | Pretty print an axiom.
prettyAxiom :: HighlightDocument d => Axiom -> d
prettyAxiom ax =
    kwAxiom <-> text (L.get axName ax) <> colon $-$
    (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get axFormula ax) $-$
    (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get axFormula ax

-- | Pretty print a lemma.
prettyLemma :: HighlightDocument d => (p -> d) -> Lemma p -> d
prettyLemma ppPrf lem =
    kwLemma <-> prettyLemmaName lem <> colon $-$
    (nest 2 $
      sep [ prettyTraceQuantifier $ L.get lTraceQuantifier lem
          , doubleQuotes $ prettyLNFormula $ L.get lFormula lem
          ]
    )
    $-$
    ppLNFormulaGuarded (L.get lFormula lem)
    $-$
    ppPrf (L.get lProof lem)
  where
    ppLNFormulaGuarded fm = case formulaToGuarded fm of
        Left err -> multiComment $
            text "conversion to guarded formula failed:" $$
            nest 2 err
        Right gf -> case toSystemTraceQuantifier $ L.get lTraceQuantifier lem of
          ExistsNoTrace -> multiComment
            ( text "guarded formula characterizing all counter-examples:" $-$
              doubleQuotes (prettyGuarded (gnot gf)) )
          ExistsSomeTrace -> multiComment
            ( text "guarded formula characterizing all satisfying traces:" $-$
              doubleQuotes (prettyGuarded gf) )


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
    ppStep step = sep
      [ prettyProofMethod (psMethod step)
      , if isNothing (psInfo step) then multiComment_ ["unannotated"]
                                   else emptyDoc
      ]

-- | Pretty print an closed rule.
prettyClosedProtoRule :: HighlightDocument d => ClosedProtoRule -> d
prettyClosedProtoRule cru =
    (prettyProtoRuleE ruE) $--$
    (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$ ppRuleAC)
  where
    ruAC = L.get cprRuleAC cru
    ruE  = L.get cprRuleE cru
    ppRuleAC
      | isTrivialProtoVariantAC ruAC ruE = multiComment_ ["has exactly the trivial AC variant"]
      | otherwise                        = multiComment $ prettyProtoRuleAC ruAC

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
                 ppInjectiveFactInsts
                 -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                 prettyClosedProtoRule
                 prettyIncrementalProof
                 thy
  where
    ppInjectiveFactInsts crc =
        case S.toList $ L.get crcInjectiveFactInsts crc of
            []   -> emptyDoc
            tags -> lineComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) tags ]

prettyClosedSummary :: Document d => ClosedTheory -> d
prettyClosedSummary thy =
    vcat lemmaSummaries
  where
    lemmaSummaries = do
        LemmaItem lem  <- L.get thyItems thy
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary $ L.get lProof lem
            quantifier = (toSystemTraceQuantifier $ L.get lTraceQuantifier lem)
            analysisType = parens $ prettyTraceQuantifier $ L.get lTraceQuantifier lem
        return $ text (L.get lName lem) <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))


-- | Pretty print a 'TraceQuantifier'.
prettyTraceQuantifier :: Document d => TraceQuantifier -> d
prettyTraceQuantifier ExistsTrace = text "exists-trace"
prettyTraceQuantifier AllTraces   = text "all-traces"


-- Instances: FIXME: Sort them into the right files
--------------------------------------------------

$( derive makeBinary ''TheoryItem)
$( derive makeBinary ''LemmaAttribute)
$( derive makeBinary ''TraceQuantifier)
$( derive makeBinary ''Axiom)
$( derive makeBinary ''Lemma)
$( derive makeBinary ''ClosedProtoRule)
$( derive makeBinary ''ClosedRuleCache)
$( derive makeBinary ''Theory)

$( derive makeNFData ''TheoryItem)
$( derive makeNFData ''LemmaAttribute)
$( derive makeNFData ''TraceQuantifier)
$( derive makeNFData ''Axiom)
$( derive makeNFData ''Lemma)
$( derive makeNFData ''ClosedProtoRule)
$( derive makeNFData ''ClosedRuleCache)
$( derive makeNFData ''Theory)

