-- |
-- Checked rendering modes shared by ProVerif property printers.
module Export.ProVerif.Render
  ( ppAxiomLemma,
    ppLemma,
    ppRestr,
    renderSapicFormula,
  )
where

import Control.Monad.Fresh
import Control.Monad.Trans.PreciseFresh qualified as Precise
import Data.List as List
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Maybe
import Data.Set qualified as S
import Export.Name (freshNameAvoiding)
import Export.ProVerif.Formula
import Export.ProVerif.Instrumentation
import Export.ProVerif.Property
import Export.Sapic
import Export.Types
import Sapic.Typing
import Text.PrettyPrint.Class
import Theory
import Theory.Sapic
import Theory.Text.Pretty

data EventTimeMode
  = RenderEventTime
  | OmitEventTime
  deriving (Eq, Ord, Show)

data PVElement
  = R
  | RSL
  deriving (Eq, Ord, Show)

-- | Context threaded through the formula and atom printers.
data FormulaRenderContext = FormulaRenderContext
  { renderTimeMode :: EventTimeMode,
    renderRidNames :: M.Map String String,
    renderRuleIdEvents :: S.Set String,
    renderTypingEnv :: TypingEnvironment
  }

-- | Whether an atom is rendered under a negation.
data AtomPolarity = PositiveAtom | NegatedAtom
  deriving (Eq, Ord, Show)

renderSapicFormula :: LNFormula -> Doc
renderSapicFormula formula =
  fst . snd $
    Precise.evalFresh
      (ppLFormula plainContext (ppNAtom plainContext) formula)
      (avoidPrecise formula)
  where
    plainContext = FormulaRenderContext RenderEventTime M.empty S.empty emptyTypeEnv

mergeType :: (Eq a) => Maybe a -> Maybe a -> Maybe a
mergeType t Nothing = t
mergeType _ t = t

mergeEnv :: M.Map LVar SapicType -> M.Map LVar SapicType -> M.Map LVar SapicType
mergeEnv = M.mergeWithKey (\_ t1 t2 -> Just $ mergeType t1 t2) id id

typeVarsEvent :: (Ord k) => TypingEnvironment -> FactTag -> [Term (Lit c k)] -> M.Map k SapicType
typeVarsEvent TypingEnvironment {events = ev} tag ts =
  case M.lookup tag ev of
    Just t ->
      foldl
        ( \mp (term, ty) ->
            case viewTerm term of
              Lit (Var lvar) -> M.insert lvar ty mp
              _ -> mp
        )
        M.empty
        (zip ts t)
    Nothing -> M.empty

-- | The per-occurrence rule-id variable of a timepoint variable, if any.
ridOfTerm :: FormulaRenderContext -> LNTerm -> Maybe Doc
ridOfTerm context t
  | renderTimeMode context == OmitEventTime = Nothing
  | otherwise = case viewTerm t of
      Lit (Var (LVar n LSortNode _)) -> text <$> M.lookup n (renderRidNames context)
      _ -> Nothing

ppProtoAtom ::
  FormulaRenderContext ->
  AtomPolarity ->
  (s LNTerm -> Doc) ->
  (LNTerm -> Doc) ->
  ProtoAtom s LNTerm ->
  (Doc, M.Map LVar SapicType)
ppProtoAtom context _ _ ppT (Action v f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | tag == KUFact = translationFail "KU facts are outside the supported formula translation"
  | isKLogFact f =
      (withEventTime (ppFactL "attacker" ts), M.empty)
  | otherwise =
      ( withEventTime
          ( text "event("
              <> eventArgs ('e' : factTagName tag) ts
              <> text ")"
          ),
        typeVarsEvent (renderTypingEnv context) tag ts
      )
  where
    factName = factTagName tag
    useRuleId = factName `S.member` renderRuleIdEvents context
    ppFactL n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppT t
    eventArgs n t
      | useRuleId = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ (ridDoc : map ppT t)
      | otherwise = ppFactL n t
    ridDoc = fromMaybe (text "rid") (ridOfTerm context v)
    withEventTime document =
      case renderTimeMode context of
        RenderEventTime -> document <> opAction <> ppT v
        OmitEventTime -> document
ppProtoAtom _ _ ppS _ (Syntactic s) = (ppS s, M.empty)
-- A temporal equality between rule-id instrumented events is translated as an
-- equality of their rule-id variables: distinct ProVerif events never share a
-- timepoint, while in Tamarin equal timepoints mean "same rule instance".
ppProtoAtom context polarity _ ppT (EqE l r) =
  case (ridOfTerm context l, ridOfTerm context r) of
    (Just dl, Just dr) -> (sep [dl <-> comparisonOp, dr], M.empty)
    _ -> (sep [ppT l <-> comparisonOp, ppT r], M.empty)
  where
    comparisonOp = case polarity of
      PositiveAtom -> opEqual
      NegatedAtom -> text "<>"
ppProtoAtom _ _ _ ppT (Less u v) = (ppT u <-> opLess <-> ppT v, M.empty)
ppProtoAtom _ _ _ ppT (Subterm u v) = (text "subterm(" <> ppT u <> comma <> ppT v <> text ")", M.empty)
ppProtoAtom _ _ _ _ (Last i) = (operator_ "last" <> parens (text (show i)), M.empty)

ppNAtom :: FormulaRenderContext -> AtomPolarity -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppNAtom context polarity =
  ppProtoAtom context polarity (const emptyDoc) (fst . ppLNTerm emptyTC)

extractFree :: BVar p -> p
extractFree (Free v) = v
extractFree (Bound i) = translationInvariantFail $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

toLAt :: (Ord (f1 b), Ord (f1 (BVar b)), Functor f2, Functor f1) => f2 (Term (f1 (BVar b))) -> f2 (Term (f1 b))
toLAt = fmap (mapLits (fmap extractFree))

ppLFormula ::
  (MonadFresh m, Functor syn) =>
  FormulaRenderContext ->
  (AtomPolarity -> ProtoAtom syn LNTerm -> (Doc, M.Map LVar SapicType)) ->
  ProtoFormula syn (String, LSort) Name LVar ->
  m ([LVar], (Doc, M.Map LVar SapicType))
ppLFormula context ppAt =
  printBare
  where
    keepTimeVars = renderTimeMode context == RenderEventTime

    -- Bare positions (top level, implication premise and conclusion):
    -- connective chains are rendered without enclosing parentheses, with
    -- the operator leading each continuation line.
    printBare fm = case fm of
      Conn Imp premise conclusion -> printArrow "==> " premise conclusion
      Conn Iff premise conclusion -> printArrow (render opIff ++ " ") premise conclusion
      Conn And _ _ -> printChain And "&& " fm
      Conn Or _ _ -> printChain Or "|| " fm
      _ -> printLeaf fm

    printArrow arrow premise conclusion = do
      (vsPremise, (premiseDoc, envPremise)) <- printPremise premise
      (vsConclusion, (conclusionDoc, envConclusion)) <- printConclusion conclusion
      pure
        ( vsPremise ++ vsConclusion,
          ( sep [premiseDoc, text arrow <> conclusionDoc],
            mergeEnv envPremise envConclusion
          )
        )

    -- A nested implication in premise position keeps its parentheses.
    printPremise fm@(Conn Imp _ _) = printParenthesized fm
    printPremise fm@(Conn Iff _ _) = printParenthesized fm
    printPremise fm = printBare fm

    -- A composite implication in conclusion position keeps its parentheses
    -- as well: ProVerif attaches query attributes such as [induction] to the
    -- conclusion, so @A ==> (B ==> C)[induction]@ must not lose its grouping.
    printConclusion fm
      | conclusionIsImplication fm = case fm of
          Qua {} -> withParens (printLeaf fm)
          _ -> printParenthesized fm
      | otherwise = printBare fm

    conclusionIsImplication (Qua _ _ body) = conclusionIsImplication body
    conclusionIsImplication (Conn Imp _ _) = True
    conclusionIsImplication (Conn Iff _ _) = True
    conclusionIsImplication _ = False

    printChain connective operatorText fm = do
      rendered <- mapM printOperand (flattenSame connective fm)
      let chainDoc = case map (fst . snd) rendered of
            [] -> emptyDoc
            (firstDoc : restDocs) ->
              sep (firstDoc : map (text operatorText <>) restDocs)
      pure
        ( concatMap fst rendered,
          (chainDoc, foldr (mergeEnv . snd . snd) M.empty rendered)
        )

    flattenSame connective (Conn connective' p q)
      | connective == connective' =
          flattenSame connective p ++ flattenSame connective q
    flattenSame _ fm = [fm]

    -- Composite operands of a conjunction or disjunction are parenthesized
    -- for readability; atoms stay bare. A quantified operand whose opened
    -- body is composite is parenthesized as well.
    printOperand fm@(Conn {}) = printParenthesized fm
    printOperand fm@(Qua {})
      | quantifiedConnBody fm = withParens (printLeaf fm)
    printOperand fm = printLeaf fm

    quantifiedConnBody (Qua _ _ body) = quantifiedConnBody body
    quantifiedConnBody (Conn {}) = True
    quantifiedConnBody _ = False

    printParenthesized fm = withParens (printBare fm)

    withParens rendered = do
      (vs, (doc, env)) <- rendered
      pure (vs, (parens doc, env))

    printLeaf fm = case fm of
      Ato a -> pure ([], ppAt PositiveAtom (toLAt a))
      TF True -> pure ([], (operator_ "true", M.empty))
      TF False -> pure ([], (operator_ "false", M.empty))
      Not (Ato a@(EqE _ _)) -> pure ([], ppAt NegatedAtom (toLAt a))
      Not p -> do
        (vs, (p', envp)) <- printBare p
        pure (vs, (operator_ "not" <> opParens p', envp))
      Qua {} ->
        scopeFreshness $ do
          (vs, _, fm') <- openFormulaPrefix fm
          (vsp, d') <- printBare fm'
          pure (filter (\v -> keepTimeVars || lvarSort v /= LSortNode) (vs ++ vsp), d')
      _ -> printBare fm

data DeclarationMode
  = QueryDeclaration
  | AssumptionDeclaration PVElement EventTimeMode

ppFormulaDeclaration ::
  MonadFresh m =>
  DeclarationMode ->
  FormulaRenderContext ->
  LNFormula ->
  [LVar] ->
  String ->
  m Doc
ppFormulaDeclaration mode context formula extraVariables attributes = do
  (variables, (body, variableTypes)) <- renderBody formula
  let needsSharedRuleId
        | M.null ruleIdNames = formulaUsesRuleIdEvents ruleIdEvents formula
        | otherwise =
            any
              (\(timepoint, tag) -> tag `S.member` ruleIdEvents && timepoint `M.notMember` ruleIdNames)
              (collectEventTimeVars formula)
      declaredVariables =
        [text "rid:bitstring" | needsSharedRuleId]
          ++ [text (name ++ ":bitstring") | name <- S.toList (S.fromList (M.elems ruleIdNames))]
          ++ map (ppTimeTypeVar variableTypes) (S.toList (S.fromList (extraVariables ++ variables)))
  pure $ case mode of
    QueryDeclaration ->
      sep
        [ if null declaredVariables
            then text "query;"
            else text "query " <> fsep (punctuate comma declaredVariables) <> text ";",
          nest 2 body <> text attributes <> text "."
        ]
    AssumptionDeclaration element _ ->
      sep
        [ text (declarationWord element) <> fsep (punctuate comma declaredVariables) <> text ";",
          nest 2 body <> text attributes <> text "."
        ]
  where
    ruleIdEvents = renderRuleIdEvents context
    eventTimeMode = case mode of
      QueryDeclaration -> RenderEventTime
      AssumptionDeclaration _ timeMode -> timeMode
    ruleIdNames
      | eventTimeMode == RenderEventTime = renderRidNames context
      | otherwise = M.empty
    atomContext =
      context {renderTimeMode = eventTimeMode, renderRidNames = ruleIdNames}
    atomRenderer = ppNAtom atomContext
    renderBody (Conn Imp (TF True) conclusion)
      | QueryDeclaration <- mode = do
          (variables, (conclusionDoc, variableTypes)) <-
            ppLFormula atomContext atomRenderer conclusion
          pure
            ( variables,
              ( sep [text "attacker(())", text "==> " <> conclusionDoc],
                variableTypes
              )
            )
    renderBody body =
      ppLFormula atomContext atomRenderer body
    declarationWord R = "restriction "
    declarationWord RSL = "axiom "
ppTimeTypeVar :: M.Map LVar SapicType -> LVar -> Doc
ppTimeTypeVar _ lvar@(LVar _ LSortNode _) = ppLVar lvar <> text ":time"
ppTimeTypeVar te lvar =
  case M.lookup lvar te of
    Nothing -> ppLVar lvar <> text ":bitstring"
    Just t -> ppLVar lvar <> text ":" <> text (ppType t)

-- | Rename timepoint variables whose name collides with a term variable.
-- Tamarin keeps term variables ('t') and timepoint variables ('#t') in
-- separate namespaces, but a ProVerif query has a single namespace. The term
-- variable keeps its name; the colliding timepoint gets a fresh name
-- ('#t' -> '#t1'). Timepoints still bound in the formula are renamed at their
-- binder; timepoints already opened by the caller are renamed as free
-- variables and in the extra query variables. Returns the renaming so that
-- keys of per-occurrence rule-id maps can be remapped alongside.
renameCollidingTimepoints :: LNFormula -> [LVar] -> (M.Map String String, LNFormula, [LVar])
renameCollidingTimepoints fm extravs
  | M.null renaming = (renaming, fm, extravs)
  | otherwise = (renaming, renameFrees (renameHints fm), map renameVar extravs)
  where
    hints = collectBinderHints fm
    freeVars = frees fm ++ extravs
    termNames =
      S.fromList $
        [n | (n, s) <- hints, s /= LSortNode]
          ++ [n | LVar n s _ <- freeVars, s /= LSortNode]
    nodeNames =
      S.fromList $
        [n | (n, LSortNode) <- hints]
          ++ [n | LVar n LSortNode _ <- freeVars]
    usedNames = S.fromList (map fst hints) `S.union` S.fromList (map lvarName freeVars)
    renaming =
      M.fromList . snd $
        List.mapAccumL freshen usedNames (S.toList (termNames `S.intersection` nodeNames))
    freshen used n =
      let n' = freshNameAvoiding "" used n
       in (S.insert n' used, (n, n'))

    renameHints (Qua q (n, s) p)
      | s == LSortNode, Just n' <- M.lookup n renaming = Qua q (n', s) (renameHints p)
      | otherwise = Qua q (n, s) (renameHints p)
    renameHints (Not p) = Not (renameHints p)
    renameHints (Conn c p q) = Conn c (renameHints p) (renameHints q)
    renameHints f = f

    renameFrees = apply substRename
    substRename :: LNSubst
    substRename =
      substFromList
        [ (v, varTerm (renameVar v))
          | v@(LVar n LSortNode _) <- List.nub (frees fm),
            n `M.member` renaming
        ]

    renameVar v@(LVar n LSortNode _)
      | Just n' <- M.lookup n renaming = v {lvarName = n'}
    renameVar v = v

-- | Sibling quantifiers that reuse a binder name collapse to one query
-- variable when the formula is flattened into a single ProVerif query. For
-- binders separated by a (positive) disjunction this is harmless: the merged
-- variable is used once per disjunct, and distributing an existential over a
-- disjunction is an equivalence. Binders whose scopes can be active on the
-- same conjunctive path must stay distinct, however: merging them equates
-- independent timepoints, and ProVerif rejects the result outright for time
-- variables ("Time variable also assigned"). Rename every later duplicate
-- that is not separated from all earlier same-named binders by a
-- disjunction.
renameConjunctiveDuplicateBinders :: LNFormula -> [LVar] -> LNFormula
renameConjunctiveDuplicateBinders fm extravs = snd (go True M.empty st0 fm)
  where
    st0 = (0 :: Int, M.empty :: M.Map String [M.Map Int Bool], used0)
    -- Avoid both the raw names and the printed forms ('n_i' for index i) of
    -- all binders and free variables.
    used0 =
      S.fromList (map fst hints)
        `S.union` S.fromList (map printedName (frees fm ++ extravs))
    printedName (LVar n _ 0) = n
    printedName (LVar n _ i) = n ++ "_" ++ show i
    hints = collectBinderHints fm

    -- A positive disjunction separates its branches; under negation the roles
    -- of conjunction and disjunction swap. Implication premises count as
    -- negated; premise and conclusion are not separated from each other.
    go pos w st (Conn Or p q)
      | pos = branch pos w st Or p q
    go pos w st (Conn And p q)
      | not pos = branch pos w st And p q
    go pos w st (Conn Imp p q) =
      let (st1, p') = go (not pos) w st p
          (st2, q') = go pos w st1 q
       in (st2, Conn Imp p' q')
    go pos w st (Conn c p q) =
      let (st1, p') = go pos w st p
          (st2, q') = go pos w st1 q
       in (st2, Conn c p' q')
    go pos w st (Not p) = let (st1, p') = go (not pos) w st p in (st1, Not p')
    go pos w (oid, kept, used) (Qua q (n, s) p) =
      let conflicts = any (conflicting w) (M.findWithDefault [] n kept)
          (n', used') =
            if conflicts
              then let c = freshName n used in (c, S.insert c used)
              else (n, used)
          kept' = M.insertWith (++) n' [w] kept
          (st1, p') = go pos w (oid, kept', used') p
       in (st1, Qua q (n', s) p')
    go _ _ st f = (st, f)

    branch pos w (oid, kept, used) c p q =
      let (st1, p') = go pos (M.insert oid True w) (oid + 1, kept, used) p
          (st2, q') = go pos (M.insert oid False w) st1 q
       in (st2, Conn c p' q')

    -- Two binders conflict unless some disjunction on both their paths
    -- separates them (same node, different sides).
    conflicting w w' = and (M.elems (M.intersectionWith (==) w w'))
    -- 'n_i' matches how the freshness machinery would have printed a
    -- disambiguated duplicate, keeping the output stable for formulas it
    -- already handled (nested duplicates).
    freshName name used = freshNameAvoiding "_" used name

ppFormulaEx :: DeclarationMode -> FormulaRenderContext -> LNFormula -> [LVar] -> String -> Doc
ppFormulaEx mode context originalFormula originalVariables attributes =
  Precise.evalFresh
    (ppFormulaDeclaration mode context {renderRidNames = ruleIdNames} formula variables attributes)
    (avoidPrecise formula)
  where
    (renaming, renamedFormula, variables) =
      renameCollidingTimepoints originalFormula originalVariables
    formula = renameConjunctiveDuplicateBinders renamedFormula variables
    ruleIdNames =
      M.mapKeys (\key -> M.findWithDefault key key renaming) (renderRidNames context)

renderPreparedQuery :: FormulaRenderContext -> PreparedFormula -> String -> Doc
renderPreparedQuery context prepared attributes =
  Precise.evalFresh (go formula) (avoidPrecise formula)
  where
    formula = prepared.preparedFormula
    renderFormula body variables =
      ppFormulaEx QueryDeclaration context body variables attributes
    openAndRender quantified = do
      (variables, _, body) <- openFormulaPrefix quantified
      pure (renderFormula body variables)
    go (Not quantified@(Qua Ex _ _)) = openAndRender quantified
    go quantified@(Qua Ex _ _) = openAndRender quantified
    go (Not quantified@(Qua All _ _)) = pure (renderFormula quantified [])
    go quantified@(Qua All _ _) = pure (renderFormula quantified [])
    go _ = translationInvariantFail "prepared query violated the supported-fragment invariant"


-- | Comment block for a property that could not be translated.
ppOmittedProperty :: Doc -> String -> LNFormula -> String -> Doc
ppOmittedProperty nameDoc kind formula reason =
  nameDoc
    $$ text ("(* " ++ kind ++ " translation failed: " ++ reason ++ ". *)")
    $$ text "(*" <> prettyLNFormula formula <> text "*)"
    $$ text ""

ppLemma :: S.Set String -> TypingEnvironment -> Lemma ProofSkeleton -> PropertyOutcome PreparedQueryProperty -> Doc
ppLemma _ruleIdEvents _te p (PropertyOmitted reason) =
  ppOmittedProperty (text ("(* " ++ p._lName ++ " *)")) "Lemma" p._lFormula reason
ppLemma _ _ _ PropertyExcluded = emptyDoc
ppLemma ruleIdEvents te p (PropertyEmitted prepared) =
  vcat
    ( intersperse
        (text "")
        ( vcat (lemmaNameComment : reconstructionComment)
            : map renderSubformula (NE.toList prepared.preparedQueryFormulas)
        )
    )
  where
    lemmaNameComment = text ("(* " ++ p._lName ++ " *)")
    useInduction
      | InvariantLemma `elem` p._lAttributes = "[induction]"
      | otherwise = ""
    renderSubformula queryFormula =
      vcat
        ( catMaybes [timepointComment, negationWarning]
            ++ [queryDoc]
        )
      where
        preparedFormulaPlan = queryFormula.preparedQueryBody
        timepointComment
          | preparedFormulaPlan.preparedHadTimepointSplit =
              Just (text "(* Timepoints in lemma have been split *)")
          | otherwise = Nothing
        negationWarning
          | queryFormula.preparedQueryPolarity == InvertResult =
              Just (text "(* Lemma has a leading negation, interpret ProVerif's answers accordingly! *)")
          | otherwise = Nothing
        queryDoc =
          renderPreparedQuery
            ( FormulaRenderContext
                RenderEventTime
                preparedFormulaPlan.preparedRuleIdNames
                ruleIdEvents
                te
            )
            preparedFormulaPlan
            useInduction
    reconstructionComment = case prepared.preparedQueryRecombination of
      Nothing -> []
      Just ConjoinQueryResults ->
        [text ("(* To reconstruct lemma " ++ p._lName ++ ", combine the query results with ∧. *)")]
      Just DisjoinQueryResults ->
        [text ("(* To reconstruct lemma " ++ p._lName ++ ", combine the query results with ∨. *)")]

renderPreparedAssumption ::
  PVElement ->
  S.Set String ->
  TypingEnvironment ->
  PreparedFormula ->
  String ->
  Doc
renderPreparedAssumption element ruleIdEvents typeEnvironment prepared attributes =
  Precise.evalFresh (go formula) (avoidPrecise formula)
  where
    formula = prepared.preparedFormula
    timeMode
      | prepared.preparedKeepTimeVariables = RenderEventTime
      | otherwise = OmitEventTime
    renderFormula body variables =
      ppFormulaEx
        (AssumptionDeclaration element timeMode)
        ( FormulaRenderContext
            timeMode
            prepared.preparedRuleIdNames
            ruleIdEvents
            typeEnvironment
        )
        body
        variables
        attributes
    go (Not quantified@(Qua Ex _ _)) = do
      (variables, _, body) <- openFormulaPrefix quantified
      pure (renderFormula body variables)
    go quantified@(Qua All _ _) = pure (renderFormula quantified [])
    go _ = translationInvariantFail "prepared assumption violated the supported-fragment invariant"
ppAxiomLemma :: S.Set String -> TypingEnvironment -> Lemma ProofSkeleton -> PropertyOutcome PreparedAxiomProperty -> Doc
ppAxiomLemma _ruleIdEvents _te l (PropertyOmitted reason) =
  ppOmittedProperty
    (text ("(* " ++ l._lName ++ " [reuse/source lemma not translated as axiom] *)"))
    "Axiom"
    l._lFormula
    reason
ppAxiomLemma _ _ _ PropertyExcluded = emptyDoc
ppAxiomLemma ruleIdEvents te l (PropertyEmitted prepared) =
  vcat
    ( intersperse
        (text "")
        ( vcat (nameComment : timepointComment)
            : map renderAxiom (NE.toList prepared.preparedAxiomFormulas)
        )
    )
  where
    nameComment =
      text ("(* " ++ l._lName ++ " [reuse/source lemma translated as axiom] *)")
    timepointComment =
      [ text "(* Timepoints in lemma have been split *)"
      | any preparedHadTimepointSplit prepared.preparedAxiomFormulas
      ]
    renderAxiom preparedFormulaPlan =
      renderPreparedAssumption RSL ruleIdEvents te preparedFormulaPlan ""

ppRestr :: S.Set String -> TypingEnvironment -> Restriction -> PropertyOutcome PreparedRestrictionProperty -> Doc
ppRestr _ _ restriction (PropertyOmitted reason) =
  ppOmittedProperty
    (text ("(* " ++ restriction._rstrName ++ " *)"))
    "Restriction"
    restriction._rstrFormula
    reason
ppRestr _ _ _ PropertyExcluded = emptyDoc
ppRestr ruleIdEvents typeEnvironment restriction (PropertyEmitted prepared) =
  vcat
    ( intersperse
        (text "")
        ( vcat (nameComment : timepointComment ++ originalComment)
            : map renderFormula (NE.toList prepared.preparedRestrictionFormulas)
        )
    )
  where
    nameComment = text ("(* " ++ restriction._rstrName ++ " *)")
    timepointComment =
      [ text "(* Timepoints in restriction have been split *)"
      | any preparedHadTimepointSplit prepared.preparedRestrictionFormulas
      ]
    originalComment =
      [ text "(* Original: " <> prettyLNFormula restriction._rstrFormula <> text " *)"
      | prepared.preparedRestrictionWasRewritten
      ]
    renderFormula preparedFormulaPlan =
      renderPreparedAssumption R ruleIdEvents typeEnvironment preparedFormulaPlan ""
