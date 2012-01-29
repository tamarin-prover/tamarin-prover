{-# LANGUAGE TemplateHaskell, TupleSections, DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving, TypeSynonymInstances, FlexibleInstances #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
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
  , defaultIntruderTheory
  , addProtoRule
  , addIntrRuleACs

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

  -- * Convenience exports
  , module Theory.Proof
  
  ) where

import           Prelude hiding ( (.), id )
                 
import           Data.Maybe
import           Data.Monoid (Sum(..))
import qualified Data.Set as S
import           Data.List
import           Data.Foldable (Foldable, foldMap)
import           Data.Traversable (Traversable, traverse)
import           Data.DeriveTH
                 
import           Control.Basics
import           Control.Parallel.Strategies
import           Control.DeepSeq
import           Control.Category
import qualified Control.Monad.State as MS

import           Extension.Data.Label 

import           Text.Isar
                 
import           Theory.Pretty
import           Theory.Rule
import           Theory.RuleVariants
-- import           Theory.IntruderRules
import           Theory.Proof


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
       deriving( Show )

type OpenRuleCache = [IntrRuleAC]

data ClosedRuleCache = ClosedRuleCache
       { _crcRules            :: ClassifiedRules
       , _crcUntypedCaseDists :: [CaseDistinction]
       , _crcTypedCaseDists   :: [CaseDistinction]
       }
       deriving( Eq, Ord, Show )


$(mkLabels [''ClosedProtoRule, ''ClosedRuleCache])

instance HasRuleName ClosedProtoRule where
    ruleName = ruleName . get cprRuleE


-- Relation between open and closed rule sets
---------------------------------------------

-- | All intruder rules of a set of classified rules.
intruderRules :: ClassifiedRules -> [IntrRuleAC]
intruderRules rules = do
    Rule (IntrInfo i) ps cs as <- joinAllRules rules
    return $ Rule i ps cs as

-- | Open a rule cache. Variants and precomputed case distinctions are dropped.
openRuleCache :: ClosedRuleCache -> OpenRuleCache
openRuleCache = intruderRules . get crcRules

-- | Open a protocol rule; i.e., drop variants and proof annotations.
openProtoRule :: ClosedProtoRule -> OpenProtoRule
openProtoRule = get cprRuleE

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
    ctxt0 = ProofContext sig classifiedRules []
    -- precomputing the case distinctions
    untypedCaseDists = precomputeCaseDistinctions ctxt0 [] 
    typedCaseDists   = 
        refineWithTypingAsms typingAsms ctxt0 untypedCaseDists

    -- classifying the rules
    rulesAC = (fmap IntrInfo                    <$> intrRulesAC) <|> 
              ((fmap ProtoInfo . get cprRuleAC) <$> protoRules)

    anyOf ps = partition (\x -> any ($ x) ps)

    (nonProto, proto) = 
        anyOf [ isDestrRule, isConstrRule , isFreshRule, isIRecvRule] rulesAC
    (spec, nonSpec)   = anyOf [isIRecvRule, isFreshRule]  nonProto
    (constr, destr)   = anyOf [isConstrRule] nonSpec
    -- FIXME: Learn, knows, fresh, etc. are special rules

    -- and sort them into ClassifiedRules datastructure for later use in proofs
    classifiedRules = ClassifiedRules
      { _crConstruct  = constr
      , _crDestruct   = destr
      , _crProtocol   = proto
      , _crSpecial    = spec
      }



------------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------------

data LemmaAttribute = 
         TypingLemma
       | ReuseLemma
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
       deriving( Show )

$(mkLabels [''Lemma])


-- Instances
------------

instance Functor Lemma where
    fmap f (Lemma n fE fAC atts prf) = Lemma n fE fAC atts (f prf)

instance Foldable Lemma where
    foldMap f = f . get lProof

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
  | TypingLemma `elem` get lAttributes lem = UntypedCaseDist
  | otherwise                              = TypedCaseDist
   

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
     deriving( Show, Functor )


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
theoryRules = foldTheoryItem return (const []) (const []) <=< get thyItems

-- | All lemmas of a theory.
theoryLemmas :: Theory sig c r p -> [Lemma p]
theoryLemmas = foldTheoryItem (const []) return (const []) <=< get thyItems

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addLemma :: Lemma p -> Theory sig c r p -> Maybe (Theory sig c r p)
addLemma l thy = do
    guard (isNothing $ lookupLemma (get lName l) thy)
    return $ modify thyItems (++ [LemmaItem l]) thy

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemma :: String -> Theory sig c r p -> Maybe (Theory sig c r p)
removeLemma lemmaName thy = do
    _ <- lookupLemma lemmaName thy
    return $ modify thyItems (concatMap fItem) thy
  where
    fItem   = foldTheoryItem (return . RuleItem) check (return . TextItem)
    check l = do guard (get lName l /= lemmaName); return (LemmaItem l)

-- | Find the lemma with the given name.
lookupLemma :: String -> Theory sig c r p -> Maybe (Lemma p)
lookupLemma name = find ((name ==) . get lName) . theoryLemmas

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

-- | The default intruder theory; uses Maude to perform AC
-- unification for computing the variants.
defaultIntruderTheory :: OpenTheory
defaultIntruderTheory = error "IMPLEMENT"
--    Theory "intruder_variants" emptySignaturePure subtermIntruderRules []

-- | Open a theory by dropping the closed world assumption and values whose
-- soundness dependens on it.
openTheory :: ClosedTheory -> OpenTheory
openTheory  (Theory n sig c items) = 
    Theory n (toSignaturePure sig) (openRuleCache c) 
      (map (mapTheoryItem openProtoRule incrementalToSkeletonProof) items)

-- | Find the open protocol rule with the given name.
lookupOpenProtoRule :: ProtoRuleName -> OpenTheory -> Maybe OpenProtoRule
lookupOpenProtoRule name = 
    find ((name ==) . get rInfo) . theoryRules

-- | Add a new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addProtoRule :: ProtoRuleE -> OpenTheory -> Maybe OpenTheory
addProtoRule ruE thy = do
    guard (maybe True ((ruE ==)) $ 
        lookupOpenProtoRule (get rInfo ruE) thy)
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
getIntrVariants = intruderRules . get (crcRules . thyCache)

-- | All protocol rules modulo E.
getProtoRuleEs :: ClosedTheory -> [ProtoRuleE]
getProtoRuleEs = map openProtoRule . theoryRules 

-- | Get the proof context for a lemma of the closed theory.
getProofContext :: CaseDistKind -> ClosedTheory -> ProofContext
getProofContext kind thy = ProofContext
    ( get thySignature          thy)
    ( get (crcRules . thyCache) thy)
    ( get (cases . thyCache)    thy)
  where
    cases = case kind of UntypedCaseDist -> crcUntypedCaseDists
                         TypedCaseDist   -> crcTypedCaseDists

-- | The classified set of rules modulo AC in this theory.
getClassifiedRules :: ClosedTheory -> ClassifiedRules
getClassifiedRules = get (crcRules . thyCache)

-- | The precomputed case distinctions.
getCaseDistinction :: CaseDistKind -> ClosedTheory -> [CaseDistinction]
getCaseDistinction UntypedCaseDist = get (crcUntypedCaseDists . thyCache)
getCaseDistinction TypedCaseDist   = get (crcTypedCaseDists . thyCache)


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
    -- FIXME: use the right Maude sig
    sig <- toSignatureWithMaude maudePath allMaudeSig $ get thySignature thy0
    let cache     = closeRuleCache typAsms sig rules $ get thyCache thy0
        addSorrys = checkAndExtendProver (sorryProver "not yet proven")

        -- Maude / Signature handle
        hnd = sigmMaudeHandle sig

        -- close all theory items: in parallel
        items = (closeTheoryItem <$> get thyItems thy0) `using` parList rdeepseq
        closeTheoryItem = foldTheoryItem 
            (RuleItem . closeProtoRule hnd) 
            (LemmaItem . ensureFormulaAC . fmap skeletonToIncrementalProof)
            TextItem

        -- extract typing lemmas
        typAsms = do 
            LemmaItem lem <- items
            guard (TypingLemma `elem` get lAttributes lem)
            let toGuarded = fmap negateGuarded . fromFormulaNegate
            case toGuarded <$> get lFormulaAC lem of
              Just (Right gf) -> return gf
              Just (Left err) -> error $ "closeTheory: " ++ err
              _               -> mzero

        -- extract protocol rules
        rules    = theoryRules (Theory errClose errClose errClose items)
        errClose = error "closeTheory"

    return $ proveTheory addSorrys $ Theory (get thyName thy0) sig cache items


-- Applying provers
-------------------

-- | A list of proof methods that could be applied to the given sequent.
applicableProofMethods :: ClosedTheory -> Sequent -> [ProofMethod]
applicableProofMethods thy se = do
    m <- possibleProofMethods (get pcSignature ctxt) se
    guard (isJust $ execProofMethod ctxt m se)
    return m
  where
    ctxt = getProofContext (get sCaseDistKind se) thy

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
        kind    = lemmaCaseDistKind l
        se      = formulaToSequent kind preItems $ fromJust $ get lFormulaAC l
        ctxt    = getProofContext kind thy
        add prf = fromMaybe prf $ runProver prover ctxt se prf

-- | Convert a formula modulo AC to a sequent.
formulaToSequent :: CaseDistKind -> [TheoryItem r p] -> FormulaAC -> Sequent
formulaToSequent kind lems = 
    addLemmasToSequent lems . sequentFromFormula kind

-- | Add the lemmas that have an associated AC variant to this sequent.
addLemmasToSequent :: [TheoryItem r p] -> Sequent -> Sequent
addLemmasToSequent items se = 
    modify sLemmas (S.union gfs) se 
  where
    gfs = S.fromList $ gatherReusableLemmas (get sCaseDistKind se) items

-- | Gather reusable lemmas to be added to a sequent.
gatherReusableLemmas :: CaseDistKind -> [TheoryItem r p] -> [LNGuarded]
gatherReusableLemmas kind items = do
    LemmaItem lem <- items
    guard $ lemmaCaseDistKind lem <= kind && 
            ReuseLemma `elem` get lAttributes lem
    Just (Right gf) <- [fromFormula <$> get lFormulaAC lem]
    return gf

-- | Ensure that the AC variant of a formula is present.
ensureFormulaAC :: Lemma p -> Lemma p
ensureFormulaAC l =
    set lFormulaAC (Just fmAC) l
  where
    -- FIXME: AC-variant of formula is formula itself.
    --        This is ensured by well-formed check (not implemented yet).
    fmAC = fromMaybe (get lFormulaE l) $ get lFormulaAC l


------------------------------------------------------------------------------
-- References to lemmas
------------------------------------------------------------------------------

-- | Lemmas are referenced by their name.
type LemmaRef = String

-- | Resolve a path in a theory. 
lookupLemmaProof :: LemmaRef -> ClosedTheory -> Maybe IncrementalProof
lookupLemmaProof name thy = get lProof <$> lookupLemma name thy

-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProof :: Prover -> LemmaRef -> ClosedTheory -> Maybe ClosedTheory
modifyLemmaProof prover name thy = 
    modA thyItems changeItems thy
  where
    findLemma (LemmaItem lem) = name == get lName lem
    findLemma _               = False

    change preItems (LemmaItem l0) = do
         let l1   = ensureFormulaAC l0
             kind = lemmaCaseDistKind l1
             ctxt = getProofContext kind thy
         se <- formulaToSequent kind preItems <$> get lFormulaAC l1
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
    [ kwTheoryHeader $ get thyName thy
    , nest 1 $ ppSig $ get thySignature thy
    , ppCache $ get thyCache thy 
    ] ++
    parMap rdeepseq ppItem (get thyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldTheoryItem 
        ppRule (prettyLemma ppPrf) (\(h,c) -> prettyFormalComment h c)

-- | Pretty print the lemma name together with its attributes.
prettyLemmaName :: HighlightDocument d => Lemma p -> d
prettyLemmaName l = case get lAttributes l of
      [] -> text (get lName l)
      as -> text (get lName l) <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)
  where
    prettyLemmaAttribute TypingLemma = text "typing"
    prettyLemmaAttribute ReuseLemma  = text "reuse"

-- | Pretty print a lemma.
prettyLemma :: HighlightDocument d => (p -> d) -> Lemma p -> d
prettyLemma ppPrf l =
    kwLemmaModulo "E" <-> prettyLemmaName l <> colon $-$ 
    (nest 2 $ doubleQuotes $ prettyFormulaE $ get lFormulaE l)
    $-$
    maybe emptyDoc ppFormulaAC (get lFormulaAC l)
    $-$
    maybe emptyDoc ppFormulaACGuarded (get lFormulaAC l)
    $-$
    maybe emptyDoc ppFormulaACInduction (get lFormulaAC l)
    $-$
    ppPrf (get lProof l)
  where
    ppFormulaAC fmAC
      | fmAC == get lFormulaE l = multiComment_ ["proof based on the same lemma modulo AC"]
      | otherwise               =
          multiComment
              ( text "proof based on the following equivalent lemma modulo AC:" $-$
                doubleQuotes (prettyFormulaAC fmAC) )

    ppFormulaACGuarded fmAC = case fromFormulaNegate fmAC of
        Left err -> multiComment_ 
            ["conversion to doubly-guarded formula failed:", err]
        Right gf -> multiComment
            ( text "doubly-guarded formula characterizing all attacks:" $-$
              doubleQuotes (prettyGuarded gf) )

    ppFormulaACInduction fmAC = case fmInd of
        Left err -> multiComment_ 
            ["formula cannot be proven by induction:", err]
        Right gf -> multiComment
            ( text "proof by induction possible over the formula:" $-$
              doubleQuotes (prettyGuarded gf) )
      where
        fmInd = applyInduction =<< fromFormulaNegate fmAC



-- | Pretty-print a non-empty bunch of intruder rules.
prettyIntruderVariants :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntruderVariants [] = multiComment $ vsep
    [ text "No intruder variants found. You can generate and cache them using the command"
    , nest 2 (text "tamarin-prover intruder -O")
    ]
prettyIntruderVariants vs = vcat . intersperse (text "") $ map prettyIntrRuleAC vs

-- | Pretty-print the intruder variants section.
prettyIntrVariantsSection :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntrVariantsSection rules = 
    prettyFormalComment "section" " Finite Variants of the Intruder Rules " $--$
    nest 1 (prettyIntruderVariants rules)

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
    (prettyProtoRuleE  $ get cprRuleE cru) $-$ 
    (nest 2 $ ppRuleAC $ get cprRuleAC cru)
  where
    ppRuleAC ru
      | isTrivialProtoRuleAC ru = multiComment_ ["has exactly the trivial AC variant"]
      | otherwise               = multiComment $ prettyProtoRuleAC ru

-- | Pretty print an open theory.
prettyOpenTheory :: HighlightDocument d => OpenTheory -> d
prettyOpenTheory = 
    prettyTheory prettySignature 
                 prettyIntrVariantsSection prettyOpenProtoRule prettyProof

-- | Pretty print a closed theory.
prettyClosedTheory :: HighlightDocument d => ClosedTheory -> d
prettyClosedTheory = 
    prettyTheory (prettySignature)
                 (prettyIntrVariantsSection . intruderRules . get crcRules) 
                 prettyClosedProtoRule
                 prettyIncrementalProof

prettyClosedSummary :: Document d => ClosedTheory -> d
prettyClosedSummary thy =
    vcat lemmaSummaries
  where
    lemmaSummaries = do
        LemmaItem lem  <- get thyItems thy
        let (status, Sum siz) = foldProof proofStepSummary $ get lProof lem
        return $ text (get lName lem) <> colon <-> 
                 text (showProofStatus status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))

-- Instances: FIXME: Sort them into the right files
--------------------------------------------------

instance (Ord l, NFData l, NFData a) => NFData (LTree l a) where
  rnf (LNode r m) = rnf r `seq` rnf  m

$( derive makeNFData ''TheoryItem)
$( derive makeNFData ''LemmaAttribute)
$( derive makeNFData ''Lemma)
$( derive makeNFData ''ClosedRuleCache)
$( derive makeNFData ''Theory)
$( derive makeNFData ''ProofMethod)
$( derive makeNFData ''Contradiction)
$( derive makeNFData ''ProofStep)

$( derive makeNFData ''CaseDistinction)
$( derive makeNFData ''ClassifiedRules)
$( derive makeNFData ''ClosedProtoRule)
$( derive makeNFData ''BigStepGoal)
$( derive makeNFData ''ProtoRuleACInfo)
