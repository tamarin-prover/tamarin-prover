{-# LANGUAGE TemplateHaskell, TupleSections #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier & Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Types to represent proofs.
module Theory.Proof (
  -- * Utilities
    LTree(..)
  , mergeMapsWith

  -- * Types
  , ProofMethod(..)
  , ProofStep(..)
  , CaseName
  , Proof

  -- ** Paths inside proofs
  , ProofPath
  , atPath
  , insertPaths

  -- ** Folding/modifying proofs
  , mapProofInfo
  , foldProof
  , annotateProof
  , ProofStatus(..)
  , proofStepStatus

  , cutOnAttackDFS
  , cutOnAttackBFS

  -- ** Unfinished proofs
  , sorry
  , unproven

  -- ** Proof methods
  , execProofMethod
  , possibleProofMethods

  -- ** Incremental proof construction
  , IncrementalProof
  , Prover
  , runProver
  , mapProverProof

  , orelse
  , tryProver
  , sorryProver
  , oneStepProver
  , autoProver
  , boundProver
  , focus
  , checkAndExtendProver
  , replaceSorryProver
  , contradictionAndClauseProver

  -- ** Pretty Printing
  , simplifyVariableIndices
  , prettyProofMethod
  , prettyProof
  , prettyProofWith

  , showProofStatus

  -- ** Parallel Strategy for exploring a proof
  , parLTreeDFS

  -- ** Convenience exports
  , module Theory.Constraint.Solver

) where

import           Data.Binary
import           Data.DeriveTH
import           Data.Foldable                    (Foldable, foldMap)
import           Data.Function                    (on)
import           Data.Label                       hiding (get)
import qualified Data.Label                       as L
import           Data.List
import qualified Data.Map                         as M
import           Data.Maybe
import           Data.Monoid
import           Data.Ord                         (comparing)
import qualified Data.Set                         as S
import           Data.Traversable
import           Safe

import           Debug.Trace

import           Control.Basics
import           Control.DeepSeq
import           Control.Monad.Bind
import qualified Control.Monad.State              as S
import qualified Control.Monad.Trans.PreciseFresh as Precise
import           Control.Parallel.Strategies

import           Theory.Model
import           Theory.Constraint.Solver
import           Theory.Text.Pretty


------------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------------

-- | @uniqueListBy eq changes xs@ zips the @changes@ with all sequences equal
-- elements in the list.
--
-- > uniqueListBy compare id (const [ (++ show i) | i <- [1..] ]) ["a","b","a"] =
-- > ["a1","b","a2"]
--
uniqueListBy :: (a -> a -> Ordering) -> (a -> a) -> (Int -> [a -> a]) -> [a] -> [a]
uniqueListBy ord single distinguish xs0 =
      map fst
    $ sortBy (comparing snd)
    $ concat $ map uniquify $ groupBy (\x y -> ord (fst x) (fst y) == EQ)
    $ sortBy (ord `on` fst)
    $ zip xs0 [(0::Int)..]
  where
    uniquify []      = error "impossible"
    uniquify [(x,i)] = [(single x, i)]
    uniquify xs      = zipWith (\f (x,i) -> (f x, i)) dist xs
      where
        dist = distinguish $ length xs

------------------------------------------------------------------------------
-- Utility: Trees with uniquely labelled edges.
------------------------------------------------------------------------------

-- | Trees with uniquely labelled edges.
data LTree l a = LNode
     { root     :: a
     , children :: M.Map l (LTree l a)
     }
     deriving( Eq, Ord, Show )

instance Functor (LTree l) where
    fmap f (LNode r cs) = LNode (f r) (M.map (fmap f) cs)

instance Foldable (LTree l) where
    foldMap f (LNode x cs) = f x `mappend` foldMap (foldMap f) cs

instance Traversable (LTree l) where
    traverse f (LNode x cs) = LNode <$> f x <*> traverse (traverse f) cs

-- | A parallel evaluation strategy well-suited for DFS traversal: As soon as
-- a node is forced it sparks off the computation of the number of case-maps
-- of all its children. This way most of the data is already evaulated, when
-- the actual DFS traversal visits it.
--
-- NOT used for now. It sometimes required too much memory.
parLTreeDFS :: Strategy (LTree l a)
parLTreeDFS (LNode x0 cs0) = do
    cs0' <- (`parTraversable` cs0) $ \(LNode x cs) -> LNode x <$> rseq cs
    return $ LNode x0 (M.map (runEval . parLTreeDFS) cs0')

------------------------------------------------------------------------------
-- Utility: Merging maps
------------------------------------------------------------------------------

-- | /O(n+m)/. A generalized union operator for maps with differing types.
mergeMapsWith :: Ord k
              => (a -> c) -> (b -> c) -> (a -> b -> c)
              -> M.Map k a -> M.Map k b -> M.Map k c
mergeMapsWith leftOnly rightOnly combine l r =
    M.map extract $ M.unionWith combine' l' r'
  where
    l' = M.map (Left . Left)  l
    r' = M.map (Left . Right) r

    combine' (Left (Left a)) (Left (Right b)) = Right $ combine a b
    combine' _ _ = error "mergeMapsWith: impossible"

    extract (Left (Left  a)) = leftOnly  a
    extract (Left (Right b)) = rightOnly b
    extract (Right c)        = c

------------------------------------------------------------------------------
-- Proof Methods
------------------------------------------------------------------------------

-- | Sound transformations of sequents.
data ProofMethod =
    Sorry String                         -- ^ Proof was not completed
  | Attack                               -- ^ An attack was fond
  | Simplify                             -- ^ A simplification step.
  | SolveGoal Goal                       -- ^ A goal was solved.
  | Contradiction (Maybe Contradiction)
  | Induction
    -- ^ A contradiction could be derived, possibly with a reason.
  deriving( Eq, Ord, Show )

instance HasFrees ProofMethod where
    foldFrees f (SolveGoal g)     = foldFrees f g
    foldFrees f (Contradiction c) = foldFrees f c
    foldFrees _ _                 = mempty

    mapFrees f (SolveGoal g)     = SolveGoal <$> mapFrees f g
    mapFrees f (Contradiction c) = Contradiction <$> mapFrees f c
    mapFrees _ method            = pure method



------------------------------------------------------------------------------
-- Proof Steps
------------------------------------------------------------------------------

-- | A proof steps is a proof method together with additional context-dependent
-- information.
data ProofStep a = ProofStep
     { psMethod :: ProofMethod
     , psInfo   :: a
     }
     deriving( Eq, Ord, Show )

instance Functor ProofStep where
    fmap f (ProofStep m i) = ProofStep m (f i)

instance Foldable ProofStep where
    foldMap f = f . psInfo

instance Traversable ProofStep where
    traverse f (ProofStep m i) = ProofStep m <$> f i

instance HasFrees a => HasFrees (ProofStep a) where
    foldFrees f (ProofStep m i) = foldFrees f m `mappend` foldFrees f i
    mapFrees f (ProofStep m i)  = ProofStep <$> mapFrees f m <*> mapFrees f i

------------------------------------------------------------------------------
-- Proof Trees
------------------------------------------------------------------------------

-- | Every case in a proof is uniquely named.
type CaseName = String

-- | A path to a subproof.
type ProofPath = [CaseName]

-- | A proof is a tree of proof steps whose edges are labelled with case names.
type Proof a = LTree CaseName (ProofStep a)

-- Unfinished proofs
--------------------

-- | A proof using the 'sorry' proof method.
sorry :: String -> a -> Proof a
sorry reason ann = LNode (ProofStep (Sorry reason) ann) M.empty

-- | A proof denoting an unproven part of the proof.
unproven :: a -> Proof a
unproven = sorry "not yet proven"


-- Paths in proofs
------------------

-- | @prf `atPath` path@ returns the subproof at the @path@ in @prf@.
atPath :: Proof a -> ProofPath -> Maybe (Proof a)
atPath = foldM (flip M.lookup . children)

-- | @modifyAtPath f path prf@ applies @f@ to the subproof at @path@,
-- if there is one.
modifyAtPath :: (Proof a -> Maybe (Proof a)) -> ProofPath
             -> Proof a -> Maybe (Proof a)
modifyAtPath f =
    go
  where
    go []     prf = f prf
    go (l:ls) prf = do
        let cs = children prf
        prf' <- go ls =<< M.lookup l cs
        return (prf { children = M.insert l prf' cs })

-- | @insertPaths prf@ inserts the path to every proof node.
insertPaths :: Proof a -> Proof (a, ProofPath)
insertPaths =
    insertPath []
  where
    insertPath path (LNode ps cs) =
        LNode (fmap (,reverse path) ps)
              (M.mapWithKey (\n prf -> insertPath (n:path) prf) cs)


-- Utilities for dealing with proofs
------------------------------------


-- | Apply a function to the information of every proof step.
mapProofInfo :: (a -> b) -> Proof a -> Proof b
mapProofInfo = fmap . fmap

-- | @boundProofDepth bound prf@ bounds the depth of the proof @prf@ using
-- 'Sorry' steps to replace the cut sub-proofs.
boundProofDepth :: Int -> Proof a -> Proof a
boundProofDepth bound =
    go bound
  where
    go n (LNode ps@(ProofStep _ info) cs)
      | 0 < n     = LNode ps                     $ M.map (go (pred n)) cs
      | otherwise = sorry ("bound " ++ show bound ++ " hit") info

-- | Fold a proof.
foldProof :: Monoid m => (ProofStep a -> m) -> Proof a -> m
foldProof f =
    go
  where
    go (LNode step cs) = f step `mappend` foldMap go (M.elems cs)

-- | Annotate a proof in a bottom-up fashion.
annotateProof :: (ProofStep a -> [b] -> b) -> Proof a -> Proof b
annotateProof f =
    go
  where
    go (LNode step@(ProofStep method _) cs) =
        LNode (ProofStep method info') cs'
      where
        cs' = M.map go cs
        info' = f step (map (psInfo . root . snd) (M.toList cs'))

-- Proof cutting
----------------

-- | The status of a 'Proof'.
data ProofStatus =
         CompleteProof   -- ^ The proof is complete: no sorry, no attack
       | IncompleteProof -- ^ There is a sorry, but no attack.
       | TraceFound     -- ^ There is an attack

instance Monoid ProofStatus where
    mempty = CompleteProof

    mappend TraceFound _               = TraceFound
    mappend _ TraceFound               = TraceFound
    mappend IncompleteProof _           = IncompleteProof
    mappend _ IncompleteProof           = IncompleteProof
    mappend CompleteProof CompleteProof = CompleteProof

-- | The status of a 'ProofStep'.
proofStepStatus :: ProofStep a -> ProofStatus
proofStepStatus (ProofStep Attack _)    = TraceFound
proofStepStatus (ProofStep (Sorry _) _) = IncompleteProof
proofStepStatus (ProofStep _ _)         = CompleteProof

-- | @cutOnAttackDFS prf@ remove all other cases if attack is found.
-- FIXME: Probably holds onto the whole proof tree. Use iterative deepening.
cutOnAttackDFS :: Proof (Maybe System) -> Proof (Maybe System)
cutOnAttackDFS prf =
    case getFirst $ findAttacks $ insertPaths prf of
      Nothing   -> prf
      Just path -> extractAttack path prf
  where
    findAttacks (LNode (ProofStep Attack (_,path)) _) = First (Just path)
    findAttacks (LNode _ cs) = foldMap findAttacks $ M.elems cs
        {- The following "optimization" didn't work out in practice.
        foldMap findAttacks preferred `mappend` foldMap findAttacks delayed
      where
        (preferred, delayed) = parPartition prefer $ M.elems cs
        prefer = maybe False (S.null . L.get sChains) . fst . psInfo . root
        -}

    extractAttack []         p               = p
    extractAttack (label:ps) (LNode pstep m) = case M.lookup label m of
        Just subprf ->
          LNode pstep (M.fromList [(label, extractAttack ps subprf)])
        Nothing     ->
          error "Theory.Constraint.cutOnAttackDFS: impossible, extractAttack failed, invalid path"

-- | Search for attacks in a BFS manner.
cutOnAttackBFS :: Proof a -> Proof a
cutOnAttackBFS =
    go (1::Int)
  where
    go l prf =
      -- FIXME: See if that poor man's logging could be done better.
      trace ("searching for attacks at depth: " ++ show l) $
        case S.runState (checkLevel l prf) CompleteProof of
          (_, CompleteProof)   -> prf
          (_, IncompleteProof) -> go (l+1) prf
          (prf', TraceFound)  ->
              trace ("attack found at depth: " ++ show l) prf'

    checkLevel 0 (LNode  step@(ProofStep Attack _) _) =
        S.put TraceFound >> return (LNode step M.empty)
    checkLevel 0 prf@(LNode (ProofStep _ x) cs)
      | M.null cs = return prf
      | otherwise = do
          st <- S.get
          msg <- case st of
              TraceFound -> return $ "ignored (attack exists)"
              _           -> S.put IncompleteProof >> return "bound reached"
          return $ LNode (ProofStep (Sorry msg) x) M.empty
    checkLevel l (LNode step cs) =
         LNode step <$> traverse (checkLevel (l-1)) cs



-- Proof method execution
-------------------------


-- @execMethod rules method se@ checks first if the @method@ is applicable to
-- the sequent @se@. Then, it applies the @method@ to the sequent under the
-- assumption that the @rules@ describe all rewriting rules in scope.
execProofMethod :: ProofContext
                -> ProofMethod -> System -> Maybe (M.Map CaseName System)
execProofMethod ctxt method se =
    case method of
      Sorry _              -> return M.empty
      Attack
        | null (openGoals se) -> return M.empty
        | otherwise           -> Nothing
      SolveGoal goal       -> execSolveGoal goal
      Simplify             -> singleCase (/=) simplifySystem
      Induction            -> execInduction
      Contradiction _
        | null (contradictions (L.get pcSignature ctxt) se) -> Nothing
        | otherwise                                       -> Just M.empty
  where
    -- expect only one or no subcase in the given case distinction
    singleCase check m =
        case map fst $ getDisj $ execReduction m ctxt se (avoid se) of
          []                   -> return $ M.empty
          [se'] | check se se' -> return $ M.singleton "" se'
                | otherwise    -> mzero
          ses                  ->
               return $ M.fromList (zip (map show [(1::Int)..]) ses)
--             error $ "execMethod: unexpected number of sequents: " ++ show (length ses) ++
--                     render (nest 2 $ vcat $ map ((text "" $-$) . prettySystem) ses)

    -- solve the given goal
    -- PRE: Goal must be valid in this sequent.
    execSolveGoal goal = do
        return $ makeCaseNames $ map fst $ getDisj $
            runReduction solver ctxt se (avoid se)
      where
        ths    = L.get pcCaseDists ctxt
        solver = do name <- maybe (solveGoal goal)
                                  (fmap $ concat . intersperse "_")
                                  (solveWithCaseDistinction ctxt ths goal)
                    simplifySystem
                    return name

        makeCaseNames =
            M.fromListWith (error "case names not unique")
          . uniqueListBy (comparing fst) id distinguish
          where
            distinguish n =
                [ (\(x,y) -> (x ++ "_case_" ++ pad (show i), y))
                | i <- [(1::Int)..] ]
              where
                l      = length (show n)
                pad cs = replicate (l - length cs) '0' ++ cs

    -- Apply induction: possible if the sequent contains only
    -- a single formula.
    execInduction
      | se == se0 =
          case S.toList $ L.get sFormulas se of
            [gf] -> case ginduct gf of
              Right gf' -> Just $ M.singleton "induction" $
                              set sFormulas (S.singleton gf') se
              _         -> Nothing
            _    -> Nothing

      | otherwise = Nothing
      where
        se0 = set sFormulas (L.get sFormulas se) $
              set sLemmas (L.get sLemmas se)  $
              emptySystem (L.get sCaseDistKind se)

-- | A list of possibly applicable proof methods.
possibleProofMethods :: ProofContext -> System -> [ProofMethod]
possibleProofMethods ctxt se =
         ((Contradiction . Just) <$> contradictions (L.get pcSignature ctxt) se)
     <|> (case L.get pcUseInduction ctxt of
            AvoidInduction -> [Simplify, Induction]
            UseInduction   -> [Induction, Simplify]
         )
     <|> (SolveGoal <$> openGoals se)

-- | @proveSystemDFS rules se@ tries to construct a proof that @se@ is valid
-- using a depth-first-search strategy to resolve the non-determinism wrt. what
-- goal to solve next.  This proof can be of infinite depth, if the proof
-- strategy loops. Children at the same level are evaluated in parallel.
proveSystemDFS :: ProofContext -> System -> Proof System
proveSystemDFS ctxt se0 =
    prove se0 -- `using` parLTreeDFS
  where
    prove se =
        LNode (ProofStep method se) (M.map prove cases)
      where
        (method, cases) =
            headDef (Attack, M.empty) $ do
                m <- possibleProofMethods ctxt se
                (m,) <$> maybe mzero return (execProofMethod ctxt m se)


{- TODO: Test and probably improve

-- | @proveSystem rules se@ tries to construct a proof that @se@ is valid.
-- This proof may contain 'Sorry' steps, if the prover is stuck. It can also be
-- of infinite depth, if the proof strategy loops.
proveSystemIterDeep :: ProofContext -> System -> Proof System
proveSystemIterDeep rules se0 =
    fromJust $ asum $ map (prove se0 . round) $ iterate (*1.5) (3::Double)
  where
    prove :: System -> Int -> Maybe (Proof System)
    prove se bound
      | bound < 0 = Nothing
      | otherwise =
          case next of
            [] -> pure $ sorry "prover stuck => possible attack found" se
            xs -> asum $ map mkProof xs
      where
        next = do m <- possibleProofMethods se
                  (m,) <$> maybe mzero return (execProofMethod rules m se)
        mkProof (method, cases) =
            LNode (ProofStep method se) <$> traverse (`prove` (bound - 1)) cases
-}

-- | @checkProof rules se prf@ replays the proof @prf@ against the start
-- sequent @se@. A failure to apply a proof method is denoted by a resulting
-- proof step without an annotated sequent. An unhandled case is denoted using
-- the 'Sorry' proof method.
checkProof :: ProofContext
           -> (System -> Proof (Maybe System)) -- prover for new cases
           -> System
           -> Proof a
           -> Proof (Maybe a, Maybe System)
checkProof ctxt prover se (LNode (ProofStep method info) cs) =
    fromMaybe (node method (M.map noSystemPrf cs)) $ headMay $ do
        method' <- method : possibleProofMethods ctxt se
        -- FIXME: eqModuloFreshness is too strict currently as it doesn't
        -- rename variables to a canonical representative. Moreover, it screws
        -- up if there are AC symbols involved.
        guard (method `eqModuloFreshnessNoAC` method')
        cases <- maybe mzero return $ execProofMethod ctxt method' se
        return $ node method' $ checkChildren cases

  where
    node m = LNode (ProofStep m (Just info, Just se))

    -- cases = msum (execProofMethod rules method se) $

    noSystemPrf = mapProofInfo (\i -> (Just i, Nothing))

    checkChildren cases =
        mergeMapsWith unhandledCase noSystemPrf (checkProof ctxt prover) cases cs
      where
        unhandledCase = mapProofInfo ((,) Nothing) . prover



------------------------------------------------------------------------------
-- Provers: the interface to the outside world.
------------------------------------------------------------------------------

-- | Incremental proofs are used to represent intermediate results of proof
-- checking/construction.
type IncrementalProof = Proof (Maybe System)

-- | Provers whose sequencing is handled via the 'Monoid' instance.
--
-- > p1 `mappend` p2
--
-- Is a prover that first runs p1 and then p2 on the resulting proof.
newtype Prover =  Prover
          { runProver
              :: ProofContext              -- proof rules to use
              -> System                   -- original sequent to start with
              -> IncrementalProof          -- original proof
              -> Maybe IncrementalProof    -- resulting proof
          }

instance Monoid Prover where
    mempty          = Prover $ \_     _  -> return
    p1 `mappend` p2 = Prover $ \rules se ->
        runProver p1 rules se >=> runProver p2 rules se

-- | Map the proof generated by the prover.
mapProverProof :: (IncrementalProof -> IncrementalProof) -> Prover -> Prover
mapProverProof f p = Prover $ \ rules se prf -> f <$> runProver p rules se prf

-- | Prover that always fails.
failProver :: Prover
failProver = Prover (\ _ _ _ -> Nothing)

-- | Resorts to the second prover, if the first one is not successful.
orelse :: Prover -> Prover -> Prover
orelse p1 p2 = Prover $ \rules se prf ->
    runProver p1 rules se prf `mplus` runProver p2 rules se prf

-- | Try to apply a prover. If it fails, just return the original proof.
tryProver :: Prover -> Prover
tryProver =  (`orelse` mempty)

-- | Try to execute one proof step using the given proof method.
oneStepProver :: ProofMethod -> Prover
oneStepProver method = Prover $ \rules se _ -> do
    cases <- execProofMethod rules method se
    return $ LNode (ProofStep method (Just se)) (M.map (unproven . Just) cases)

-- | Replace the current proof with a sorry step and the given reason.
sorryProver :: String -> Prover
sorryProver reason = Prover $ \_ se _ -> return $ sorry reason (Just se)

-- | Bound the depth of proofs generated by the given prover.
boundProver :: Int -> Prover -> Prover
boundProver b p = Prover $ \rules se prf ->
    boundProofDepth b <$> runProver p rules se prf

-- | The standard automatic prover that ignores the existing proof and tries to
-- find one by itself.
autoProver :: Prover
autoProver = Prover $ \rules se _ ->
    -- evaluate cases in parallel
    return $ fmap (fmap Just) $ proveSystemDFS rules se

-- | Apply a prover only to a sub-proof, fails if the subproof doesn't exist.
focus :: ProofPath -> Prover -> Prover
focus []   prover = prover
focus path prover =
    Prover $ \rules _ prf -> modifyAtPath (prover' rules) path prf
  where
    prover' rules prf = do
        se <- psInfo (root prf)
        runProver prover rules se prf

-- | Check the proof and handle new cases using the given prover.
checkAndExtendProver :: Prover -> Prover
checkAndExtendProver prover0 = Prover $ \rules se prf ->
    return $ mapProofInfo snd $ checkProof rules (prover rules) se prf
  where
    unhandledCase   = sorry "unhandled case" Nothing
    prover rules se =
        fromMaybe unhandledCase $ runProver prover0 rules se unhandledCase

-- | Replace all annotated sorry steps with
replaceSorryProver :: Prover -> Prover
replaceSorryProver prover0 = Prover prover
  where
    prover rules _ = return . replace
      where
        replace prf@(LNode (ProofStep (Sorry _) (Just se)) _) =
            fromMaybe prf $ runProver prover0 rules se prf
        replace (LNode ps cases) =
            LNode ps $ M.map replace cases


-- | Use the first prover that works.
firstProver :: [Prover] -> Prover
firstProver = foldr orelse failProver

-- | Prover that does one contradiction step or one graph clause resolution
-- step.
contradictionAndClauseProver :: Prover
contradictionAndClauseProver = Prover $ \ctxt se prf ->
    runProver
        (firstProver $ map oneStepProver $
            (Contradiction . Just <$>
                contradictions (L.get pcSignature ctxt) se))
        ctxt se prf


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Consistently simplify variable indices in the proof; i.e., rename all
-- free variables in a top-down fashion using the 'Precise.FreshT'
-- transformer.
simplifyVariableIndices :: HasFrees a => Proof a -> Proof a
simplifyVariableIndices =
    go noBindings Precise.nothingUsed
  where
    go bindSt freshSt (LNode step cs) =
        case Precise.runFresh (runBindT (someInst step) bindSt) freshSt of
            ((step', bindSt'), freshSt') ->
                LNode step' (M.map (go bindSt' freshSt') cs)


prettyProofMethod :: HighlightDocument d => ProofMethod -> d
prettyProofMethod method = case method of
    Attack               -> keyword_ "SOLVED" <-> lineComment_ "trace found"
    Induction            -> keyword_ "induction"
    Sorry reason         -> fsep [keyword_ "sorry", lineComment_ reason]
    SolveGoal goal       -> hsep [keyword_ "solve(", prettyGoal goal, keyword_ ")"]
    Simplify             -> keyword_ "simplify"
    Contradiction reason ->
        fsep [ keyword_ "contradiction"
             , maybe emptyDoc (lineComment . prettyContradiction) reason
             ]

prettyProof :: HighlightDocument d => Proof a -> d
prettyProof = prettyProofWith (prettyProofMethod . psMethod) (const id)

prettyProofWith :: HighlightDocument d
                => (ProofStep a -> d)      -- ^ Make proof step pretty
                -> (ProofStep a -> d -> d) -- ^ Make whole case pretty
                -> Proof a                 -- ^ The proof to prettify
                -> d
prettyProofWith prettyStep prettyCase =
    ppPrf
  where
    ppPrf (LNode ps cs) = ppCases ps (M.toList cs)

    ppCases ps@(ProofStep Attack _) [] = prettyStep ps
    ppCases ps []                      = prettyCase ps (kwBy <> text " ")
                                           <> prettyStep ps
    ppCases ps [("", prf)]             = prettyStep ps $-$ ppPrf prf
    ppCases ps cases                   =
        prettyStep ps $-$
        (vcat $ intersperse (prettyCase ps kwNext) $ map ppCase cases) $-$
        prettyCase ps kwQED

    ppCase (name, prf) = nest 2 $
      (prettyCase (root prf) $ kwCase <-> text name) $-$
      ppPrf prf

-- | Convert a proof status to a redable string.
showProofStatus :: SystemTraceQuantifier -> ProofStatus -> String
showProofStatus ExistsNoTrace   TraceFound      = "falsified - found trace"
showProofStatus ExistsNoTrace   CompleteProof   = "verified"
showProofStatus ExistsSomeTrace CompleteProof   = "falsified - no trace found"
showProofStatus ExistsSomeTrace TraceFound      = "verified"
showProofStatus _               IncompleteProof = "analysis incomplete"


-- Derived instances
--------------------

$( derive makeBinary ''ProofMethod)
$( derive makeBinary ''ProofStep)
$( derive makeBinary ''ProofStatus)

$( derive makeNFData ''ProofMethod)
$( derive makeNFData ''ProofStep)
$( derive makeNFData ''ProofStatus)

instance (Ord l, NFData l, NFData a) => NFData (LTree l a) where
  rnf (LNode r m) = rnf r `seq` rnf  m

instance (Ord l, Binary l, Binary a) => Binary (LTree l a) where
  put (LNode r m) = put r >> put m
  get = LNode <$> get <*> get
