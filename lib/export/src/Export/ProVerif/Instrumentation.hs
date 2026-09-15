-- |
-- ProVerif instrumentation planning, timepoint provenance, and target-name allocation.
module Export.ProVerif.Instrumentation
  ( InstrumentationPlan (..),
    collectEventTimeVars,
    formulaRuleIdEventsWithOrigins,
    formulaUsesRuleIdEvents,
    guardSameActionConclusions,
    instrumentationPropertyEvents,
    makeTimeVarsDistinct,
    makeTimeVarsDistinctWithOrigins,
    ridOccurrenceNames,
    ridOccurrenceNamesWithOrigins,
    ridOccurrenceNamesWithOriginsPreservingSingle,
  )
where

import Data.List as List
import Data.Map qualified as M
import Data.Set qualified as S
import Export.Name
import Export.ProVerif.Formula
import Theory

-- | Theory-wide rule instrumentation needed to preserve relationships between
-- Tamarin action occurrences when rendering ProVerif correspondence queries.
-- Events in 'instrumentationRuleIdEvents' receive a fresh identifier for each
-- rule execution, so occurrences split from the same Tamarin timepoint can
-- still be correlated. Rules containing an event in
-- 'instrumentationCompletionTriggers' also emit
-- 'instrumentationCompletionEvent' after their other actions; this prevents a
-- conclusion event from satisfying a query before the corresponding rule has
-- completed.
data InstrumentationPlan = InstrumentationPlan
  { -- | Internal event name used to mark completion of an instrumented rule.
    instrumentationCompletionEvent :: String,
    -- | Source action names whose ProVerif events carry a rule-execution ID.
    instrumentationRuleIdEvents :: S.Set String,
    -- | Source action names identifying rules that emit the completion event.
    instrumentationCompletionTriggers :: S.Set String
  }
  deriving (Eq, Show)

instrumentationPropertyEvents :: InstrumentationPlan -> S.Set String
instrumentationPropertyEvents plan
  | S.null plan.instrumentationCompletionTriggers = plan.instrumentationRuleIdEvents
  | otherwise =
      S.insert plan.instrumentationCompletionEvent plan.instrumentationRuleIdEvents

timeVarNameIn :: [(String, LSort)] -> VTerm Name (BVar LVar) -> Maybe String
timeVarNameIn ctx t = case viewTerm t of
  Lit (Var (Bound i)) -> case drop (fromIntegral i) ctx of
    (n, LSortNode) : _ -> Just n
    _ -> Nothing
  Lit (Var (Free v)) | lvarSort v == LSortNode -> Just (lvarName v)
  _ -> Nothing

-- | Collect (time variable name, fact tag name) pairs for all action atoms
-- that are translated to ProVerif events (i.e. excluding K/KU facts).
collectEventTimeVars :: LNFormula -> [(String, String)]
collectEventTimeVars = go []
  where
    go ctx (Ato (Action tv f@(Fact tag _ _)))
      | tag == KUFact || isKLogFact f = []
      | otherwise = maybe [] (\n -> [(n, factTagName tag)]) (timeVarNameIn ctx tv)
    go ctx (Not p) = go ctx p
    go ctx (Conn _ p q) = go ctx p ++ go ctx q
    go ctx (Qua _ v p) = go (v : ctx) p
    go _ _ = []

-- | Add an internal completion event to correspondence premises whose
-- conclusions observe another event from the same original Tamarin action.
-- The completion event uses the premise action's timepoint only as
-- provenance: shared-timepoint splitting gives it a distinct ProVerif time
-- while retaining the same rule identifier.
--
-- The returned fact tags are the rule actions whose presence demands
-- completion emission.  No rule or protocol name is inspected.
guardSameActionConclusions :: String -> LNFormula -> (LNFormula, S.Set String)
guardSameActionConclusions completionEvent fm =
  let unique = makeBinderHintsGloballyUnique fm
      (guarded, triggers, changed) = go unique
   in if changed then (guarded, triggers) else (fm, S.empty)
  where
    go (Conn And left right) =
      let (left', leftTriggers, leftChanged) = go left
          (right', rightTriggers, rightChanged) = go right
       in ( Conn And left' right',
            leftTriggers `S.union` rightTriggers,
            leftChanged || rightChanged
          )
    go formula =
      case guardCorrespondence formula of
        Just (guarded, triggers) -> (guarded, triggers, True)
        Nothing -> (formula, S.empty, False)

    guardCorrespondence formula =
      let (prefix, body) = collectQuantifierPrefix All formula
          ctx = reverse prefix
       in case (prefix, body) of
            (_ : _, Conn Imp premise conclusion) ->
              let premiseOccurrences = collectOccurrences ctx premise
                  conclusionOccurrences = collectOccurrences ctx conclusion
                  demandingConclusionOrigins =
                    S.fromList
                      [ origin
                      | occurrence@(origin, _, _, _) <- conclusionOccurrences,
                        occurrence `notElem` premiseOccurrences
                      ]
                  sharedPremiseOccurrences =
                    [ occurrence
                    | occurrence@(origin, _, _, _) <- premiseOccurrences,
                      origin `S.member` demandingConclusionOrigins
                    ]
                  -- fromListWith receives the new value first, so this keeps
                  -- the last premise occurrence for each origin. Any member
                  -- is semantically sufficient because the split occurrences
                  -- share one allocated rule identifier.
                  lastPerOrigin =
                    M.elems $
                      M.fromListWith
                        const
                        [ (origin, occurrence)
                        | occurrence@(origin, _, _, _) <- sharedPremiseOccurrences
                        ]
                  completionActions =
                    [ Ato (Action timepoint completionFact)
                    | (_, timepoint, _, _) <- lastPerOrigin
                    ]
                  triggers =
                    S.fromList
                      [ tag
                      | (_, _, tag, _) <- sharedPremiseOccurrences
                      ]
               in if null completionActions
                    then Nothing
                    else
                      Just
                        ( rewrapBoundPrefix All prefix $
                            Conn Imp
                              (buildConjunction (premise : completionActions))
                              conclusion,
                          triggers
                        )
            _ -> Nothing

    collectOccurrences ctx (Ato (Action timepoint fact@(Fact tag _ _)))
      | tag == KUFact
          || isKLogFact fact
          || factTagName tag == completionEvent =
          []
      | Just origin <- timeOriginIn ctx timepoint =
          [(origin, timepoint, factTagName tag, fact)]
    collectOccurrences ctx (Not body) = collectOccurrences ctx body
    collectOccurrences ctx (Conn _ left right) =
      collectOccurrences ctx left ++ collectOccurrences ctx right
    collectOccurrences ctx (Qua _ v body) =
      collectOccurrences (v : ctx) body
    collectOccurrences _ _ = []

    timeOriginIn ctx term =
      case viewTerm term of
        Lit (Var (Bound i)) ->
          case drop (fromIntegral i) ctx of
            (name, LSortNode) : _ -> Just (Right name)
            _ -> Nothing
        Lit (Var (Free v))
          | lvarSort v == LSortNode -> Just (Left v)
        _ -> Nothing

    completionFact =
      Fact
        (ProtoFact Linear completionEvent 0)
        S.empty
        []

-- | Collect pairs of time-variable names linked by a temporal equality:
-- an equality atom #i = #j (possibly negated), or a negated strict
-- comparison not(#i < #j), which is expanded later into a disjunction
-- containing the equality.
collectTemporalEqPairs :: LNFormula -> [(String, String)]
collectTemporalEqPairs = go []
  where
    go ctx (Ato (EqE left right)) = pairOf ctx left right
    go ctx (Not (Ato (Less left right))) = pairOf ctx left right
    go ctx (Not body) = go ctx body
    go ctx (Conn _ left right) = go ctx left ++ go ctx right
    go ctx (Qua _ binder body) = go (binder : ctx) body
    go _ _ = []

    pairOf ctx left right =
      case (timeVarNameIn ctx left, timeVarNameIn ctx right) of
        (Just leftName, Just rightName)
          | leftName /= rightName -> [(leftName, rightName)]
        _ -> []

-- | Per-occurrence rule-id variable names for rule-id instrumented events in
-- formulas without split timepoints. The shared "rid" variable is only
-- meaningful for split-timepoint groups, whose copies it ties to the same
-- rule instance; reusing it across independent event occurrences would
-- silently constrain them to the same rule instance. Instead, each event
-- occurrence gets its own rule-id variable, named after its time variable.
--
-- This also gives temporal equalities that survive rewriting (e.g. in
-- disjunctions such as at-or-before: #j < #i | #j = #i) a translation: in
-- ProVerif, distinct events never share a timepoint, so a timepoint equality
-- would be unsatisfiable there. Since in Tamarin equal timepoints mean "same
-- rule instance", such an equality is translated as an equality between the
-- rule-id variables of the two events instead.
--
-- Only time variables used by exactly one instrumented event are mapped;
-- anything else falls back to the shared "rid" scheme.
ridOccurrenceNames :: S.Set String -> LNFormula -> M.Map String String
ridOccurrenceNames ruleIdEvents fm =
  addFreshSharedFallback fm sharedTimeNames
    $ freshenRuleIdNames fm
    $ M.fromSet ("rid_" ++) mapped
  where
    eventTVs = collectEventTimeVars fm
    tagsOf n = [tag | (n', tag) <- eventTVs, n' == n]
    mapped =
      S.fromList
        [ n
        | (n, _) <- eventTVs,
          case tagsOf n of
            [tag] -> tag `S.member` ruleIdEvents
            _ -> False
        ]
    sharedTimeNames =
      S.fromList
        [ name
        | (name, tag) <- eventTVs,
          tag `S.member` ruleIdEvents,
          name `S.notMember` mapped
        ]

-- | Per-occurrence rule-id names after shared timepoints have been split.
-- Independent original Tamarin timepoints keep distinct rule ids, while all
-- event occurrences copied from one original timepoint use the same rule id.
ridOccurrenceNamesWithOrigins ::
  S.Set String ->
  M.Map String String ->
  LNFormula ->
  M.Map String String
ridOccurrenceNamesWithOrigins ruleIdEvents splitOrigins afterSplit =
  freshenRuleIdNames afterSplit
    $ M.fromList
      [ (name, "rid_" ++ M.findWithDefault name name splitOrigins)
      | name <- S.toList eventTimeNames,
        let tags = tagsOf name,
        not (null tags),
        all (`S.member` ruleIdEvents) tags
      ]
  where
    eventTVs = collectEventTimeVars afterSplit
    eventTimeNames = S.fromList (map fst eventTVs)
    tagsOf name = [tag | (name', tag) <- eventTVs, name' == name]

-- | Use origin-aware rule ids only when a rendered formula contains more
-- than one original instrumented timepoint group. With one group, the
-- established shared @rid@ rendering is semantically identical and is kept
-- byte-for-byte.
ridOccurrenceNamesWithOriginsPreservingSingle ::
  S.Set String ->
  M.Map String String ->
  LNFormula ->
  M.Map String String
ridOccurrenceNamesWithOriginsPreservingSingle ruleIdEvents splitOrigins fm =
  if S.size (S.fromList (M.elems names)) <= 1
    then addFreshSharedFallback fm (M.keysSet names) M.empty
    else names
  where
    names = ridOccurrenceNamesWithOrigins ruleIdEvents splitOrigins fm

freshenRuleIdNames :: LNFormula -> M.Map String String -> M.Map String String
freshenRuleIdNames formula names =
  fmap (replacements M.!) names
  where
    (_, replacements) =
      foldl'
        allocatePreferred
        (formulaVariableAllocator formula, M.empty)
        (S.toAscList (S.fromList (M.elems names)))
    allocatePreferred (allocator, allocated) preferred =
      let (TargetVariable chosen, allocator') = allocateVariable preferred allocator
       in (allocator', M.insert preferred chosen allocated)

addFreshSharedFallback :: LNFormula -> S.Set String -> M.Map String String -> M.Map String String
addFreshSharedFallback formula timeNames names
  | S.null timeNames = names
  | chosen == "rid" = names
  | otherwise = foldr (`M.insert` chosen) names timeNames
  where
    allocator =
      reserveNames
        VariableNamespace
        (S.fromList (M.elems names))
        (formulaVariableAllocator formula)
    (TargetVariable chosen, _) = allocateVariable "rid" allocator

formulaVariableAllocator :: LNFormula -> NameAllocator
formulaVariableAllocator formula =
  reserveNames VariableNamespace variableNames emptyNameAllocator
  where
    variableNames =
      S.fromList
        ( map (sanitizeSymbol 'a' . fst) (collectBinderHints formula)
            ++ [ sanitizeSymbol 'a' name
               | LVar name _ _ <- frees formula
               ]
        )

-- | Event tags linked by temporal equalities that survive rewriting; these
-- need rule-id instrumentation so the equality can be translated as a
-- rule-id equality (see 'ridOccurrenceNames').
temporalEqualityLinkedEvents :: LNFormula -> S.Set String
temporalEqualityLinkedEvents fm =
  S.fromList $
    concat
      [ tagsOf leftName ++ tagsOf rightName
      | (leftName, rightName) <- collectTemporalEqPairs fm,
        not (null (tagsOf leftName)),
        not (null (tagsOf rightName))
      ]
  where
    eventTVs = collectEventTimeVars fm
    tagsOf name = [tag | (name', tag) <- eventTVs, name' == name]

-- | Binder-identity-based variant used for temporal equalities introduced by
-- the current query rewrite. It avoids adding new instrumentation because two
-- independent scopes happen to reuse the same binder hint.
temporalEqualityLinkedEventsByBinder :: LNFormula -> S.Set String
temporalEqualityLinkedEventsByBinder fm =
  S.fromList $
    concat
      [ M.findWithDefault [] a actionMap
          ++ M.findWithDefault [] b actionMap
      | (a, b) <- collectTemporalEqKeyPairs fm,
        M.member a actionMap,
        M.member b actionMap
      ]
  where
    actionMap = collectActionsWithTimepoints fm

-- | Make time variables distinct for each action occurrence in a formula.
-- This ensures that events with shared timepoints in Tamarin get distinct time variables in ProVerif.
-- Transforms: ∃ x #i. A(x)@i & B(x)@i  into  ∃ x #i1 #i2. A(x)@i1 & B(x)@i2
makeTimeVarsDistinct :: LNFormula -> LNFormula
makeTimeVarsDistinct = fst . makeTimeVarsDistinctWithOrigins

-- | Split shared timepoint variables and record the original Tamarin
-- timepoint of every generated binder hint. The provenance map is consumed
-- by rule-ID rendering: generated copies from one timepoint share a rule ID,
-- while independent original timepoints never do.
makeTimeVarsDistinctWithOrigins ::
  LNFormula ->
  (LNFormula, M.Map String String)
makeTimeVarsDistinctWithOrigins fm =
  let sharedTimeVars = findSharedTimeVars fm
      reservedNames = collectBinderHintNames fm
      splitNames = allocateSplitNames reservedNames (M.toList sharedTimeVars)
      splitOrigins =
        M.fromList
          [ (generated, origin)
          | (origin, generatedNames) <- M.elems splitNames,
            generated <- generatedNames
          ]
   in if M.null sharedTimeVars
        then (fm, M.empty)
        else (splitTimeVars splitNames fm, splitOrigins)
  where

    allocateSplitNames used0 shared =
      let (_, _, allocated) =
            foldl allocateOne (used0, S.empty, M.empty) shared
       in allocated

    allocateOne (used, usedOrigins, allocated) (key@(name, _), count) =
      let origin = freshOrigin name usedOrigins
          (used', generatedNames) =
            List.mapAccumL allocateGenerated used [name ++ show i | i <- [1 .. count]]
       in
        ( used',
          S.insert origin usedOrigins,
          M.insert key (origin, generatedNames) allocated
        )

    allocateGenerated used candidate =
      let generated = freshNameAvoiding "_" used candidate
       in (S.insert generated used, generated)

    freshOrigin name usedOrigins = freshNameAvoiding "_" usedOrigins name

-- | Find time variables (LSortNode quantifiers) that are used more than once
-- Returns: Map from (variable name, quantifier depth) to occurrence count
-- Note: quantifier depth is where the quantifier appears, not the Bound index from action perspective
findSharedTimeVars :: LNFormula -> M.Map (String, Integer) Int
findSharedTimeVars fm =
  M.filter (> 1) $ countTimeVarOccurrences [] 0 fm M.empty
  where
    -- ctx: list of (name, sort) for each quantifier (newest first)
    -- depth: current depth (number of enclosing quantifiers)
    countTimeVarOccurrences :: [(String, LSort)] -> Integer -> LNFormula -> M.Map (String, Integer) Int -> M.Map (String, Integer) Int
    countTimeVarOccurrences ctx depth (Ato (Action timeVar _fact)) acc =
      case viewTerm timeVar of
        Lit (Var (Bound idx)) | idx < depth ->
          -- Compute quantifier depth: if action is at depth D and uses Bound B,
          -- the quantifier is at depth (D - B - 1)
          let quantifierDepth = depth - idx - 1
          in case drop (fromIntegral idx) ctx of
               (name, LSortNode) : _ ->
                 M.insertWith (+) (name, quantifierDepth) 1 acc
               _ -> acc
        _ -> acc
    countTimeVarOccurrences ctx depth (Conn _ p q) acc =
      let acc' = countTimeVarOccurrences ctx depth p acc
      in countTimeVarOccurrences ctx depth q acc'
    countTimeVarOccurrences ctx depth (Not p) acc = countTimeVarOccurrences ctx depth p acc
    countTimeVarOccurrences ctx depth (Qua _q (name, varSort) p) acc =
      countTimeVarOccurrences ((name, varSort) : ctx) (depth + 1) p acc
    countTimeVarOccurrences _ _ _ acc = acc

-- | Split time variables that occur multiple times. The caller supplies
-- collision-free generated binder names together with the rule-ID origin
-- represented by each group.
splitTimeVars ::
  M.Map (String, Integer) (String, [String]) ->
  LNFormula ->
  LNFormula
splitTimeVars splitNames fm =
  fst $ splitAndReindexTimeVars [] 0 0 M.empty fm
  where
    -- ctx: list of (name, sort, original_depth) for tracking quantifiers
    -- depth: current depth (adjusted as we add quantifiers)
    -- originalDepth: the depth in the original formula (before any splits)
    -- seenCounts: tracks how many times we've seen each (originalName, originalDepth)
    splitAndReindexTimeVars :: [(String, LSort, Integer)] -> Integer -> Integer -> M.Map (String, Integer) Int -> LNFormula
       -> (LNFormula, M.Map (String, Integer) Int)

    splitAndReindexTimeVars ctx depth originalDepth seenCounts (Qua q (name, srt) p) =
      -- Check if this quantifier is a shared time variable
      -- Use originalDepth for lookup since splitNames was computed from the
      -- original formula.
      let lookupKey = (name, originalDepth)
      in case M.lookup lookupKey splitNames of
        Just (_, generatedNames) | srt == LSortNode ->
          -- This is a shared time variable - split it into multiple quantifiers
          let count = length generatedNames
              makeQuantifiers [] body = body
              makeQuantifiers (newName : rest) body =
                Qua q (newName, srt) (makeQuantifiers rest body)
              -- Shift indices in p by (count - 1) because we're adding (count - 1) extra quantifiers
              p_shifted = shiftFreeIndices (fromIntegral (count - 1)) p
              -- Process the shifted body with updated context
              -- Add count entries to context (one for each new quantifier)
              -- IMPORTANT: Store the original name (before splitting), not the split name
              newCtxEntries = [(name, srt, originalDepth) | _ <- [1..count]]
              (p', seenCounts') = splitAndReindexTimeVars (newCtxEntries ++ ctx) (depth + fromIntegral count) (originalDepth + 1) seenCounts p_shifted
          in (makeQuantifiers generatedNames p', seenCounts')
        _ ->
          -- Normal quantifier - just process recursively
          let (p', seenCounts') = splitAndReindexTimeVars ((name, srt, originalDepth) : ctx) (depth + 1) (originalDepth + 1) seenCounts p
          in (Qua q (name, srt) p', seenCounts')

    splitAndReindexTimeVars ctx depth _originalDepth seenCounts (Ato (Action timeVar fact)) =
      case viewTerm timeVar of
        Lit (Var (Bound idx)) | idx < depth ->
          -- Check if this bound variable refers to a split time variable
          case drop (fromIntegral idx) ctx of
            (origName, LSortNode, origDepth) : _ ->
              let lookupKey = (origName, origDepth)
              in -- Check if the original quantifier was split
              case M.lookup lookupKey splitNames of
                Just (_, generatedNames) | length generatedNames > 1 ->
                  -- This action uses a split time variable
                  -- Determine which occurrence this is
                  let key = (origName, origDepth)
                      currentCount = M.findWithDefault 0 key seenCounts
                      newSeenCounts = M.insert key (currentCount + 1) seenCounts
                      -- Adjust the Bound index: subtract currentCount because j1 is furthest, j2 is closest
                      -- If original was Bound idx, first occurrence uses Bound idx, second uses Bound (idx-1), etc.
                      newIdx = idx - fromIntegral currentCount
                      newTimeVar = lit $ Var $ Bound newIdx
                  in (Ato (Action newTimeVar fact), newSeenCounts)
                _ -> (Ato (Action timeVar fact), seenCounts)
            _ -> (Ato (Action timeVar fact), seenCounts)
        _ -> (Ato (Action timeVar fact), seenCounts)

    splitAndReindexTimeVars ctx depth originalDepth seenCounts (Conn c p q) =
      let (p', seenCounts') = splitAndReindexTimeVars ctx depth originalDepth seenCounts p
          (q', seenCounts'') = splitAndReindexTimeVars ctx depth originalDepth seenCounts' q
      in (Conn c p' q', seenCounts'')

    splitAndReindexTimeVars ctx depth originalDepth seenCounts (Not p) =
      let (p', seenCounts') = splitAndReindexTimeVars ctx depth originalDepth seenCounts p
      in (Not p', seenCounts')

    splitAndReindexTimeVars _ _ _ seenCounts f = (f, seenCounts)

formulaUsesRuleIdEvents :: S.Set String -> ProtoFormula syn (a, LSort) c LVar -> Bool
formulaUsesRuleIdEvents ruleIdEvents =
  foldFormula
    ( \case
        Action _ (Fact tag _ _) -> factTagName tag `S.member` ruleIdEvents
        _ -> False
    )
    (const False)
    id
    (\_ p q -> p || q)
    (\_ _ p -> p)

-- | Events in one formula that require rule-instance instrumentation.
-- Definite temporal equalities are eliminated by unifying the equated
-- timepoints, turning them into shared timepoints; equalities that survive
-- (e.g. in disjunctions) are translated as rule-id equalities.
eventsRequiringRuleIds :: LNFormula -> S.Set String
eventsRequiringRuleIds fm =
  let fm' = eliminateTemporalEqualities fm
   in eventsSharingTimepoints fm' `S.union` temporalEqualityLinkedEvents fm'

formulaRuleIdEventsWithOrigins :: M.Map String String -> LNFormula -> S.Set String
formulaRuleIdEventsWithOrigins timeOrigins formula =
  eventsRequiringRuleIds formula
    `S.union` temporalEqualityLinkedEventsByBinder formula
    `S.union` splitOriginEvents
  where
    splitOriginEvents =
      S.fromList
        [ tag
        | (timepoint, tag) <- collectEventTimeVars formula,
          timepoint `M.member` timeOrigins
        ]
