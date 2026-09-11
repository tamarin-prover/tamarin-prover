-- |
-- Backend-neutral SAPIC export context shared by target renderers.
module Export.Sapic
  ( ensureAttackerContext,
    formalCommentDocs,
    headerOfFunSym,
    loadDiffProc,
    loadEquivProc,
    loadHeaders,
    loadMacroProc,
    loadProc,
    ppLNTerm,
    ppLVar,
    ppType,
  )
where

import Control.Monad.Fresh
import Data.ByteString.Char8 qualified as BC
import Data.List as List
import Data.Map qualified as M
import Data.Maybe
import Data.Set qualified as S
import Export.Name (sanitizeSymbol)
import Export.ProVerif.Header
import Export.ProVerif.Rule
import Export.Types
import Sapic.Annotation
import Sapic.Facts (stripNonAlphanumerical)
import Sapic.Report
import Sapic.States
import Sapic.Typing
import Term.SubtermRule
import Text.PrettyPrint.Class
import Theory
import Theory.Sapic


ppPubName :: NameId -> Doc
ppPubName (NameId n) = text $ case n of
  "zero" -> "0"
  "one" -> "1"
  "g" -> "g"
  _ -> "v" ++ n


------------------------------------------------------------------------------
-- Term Printers
------------------------------------------------------------------------------

-- | Print a variable name. For timepoint (node) variables, we need to ensure
-- they don't collide with term variables of the same name. In Tamarin, #t and t
-- are different variables, but in ProVerif they would both become 't'.
-- We handle this by checking the sort and NOT adding a prefix here - instead,
-- we use a separate function for timepoint variables in query declarations.
ppLVar :: LVar -> Doc
ppLVar (LVar n _ 0) = text $ sanitizeSymbol 'a' n
ppLVar (LVar n _ i) = text . sanitizeSymbol 'a' $ n <> "_" <> show i

ppUnTypeVar :: SapicLVar -> Doc
ppUnTypeVar (SapicLVar lvar _) = ppLVar lvar

ppType :: Maybe String -> String
ppType Nothing = "bitstring"
ppType (Just s) = s

ppTypeVar :: TranslationContext -> SapicLVar -> Doc
ppTypeVar tc v@(SapicLVar lvar ty) = case trans tc of
  ProVerif -> ppLVar lvar <> text ":" <> text (ppType ty)
  DeepSec -> ppUnTypeVar v

ppTypeLit :: (Show c) => TranslationContext -> Lit c SapicLVar -> Doc
ppTypeLit tc (Var v) = ppTypeVar tc v
ppTypeLit _ (Con c) = text . sanitizeSymbol 'a' $ show c

-- | Render a term and collect required ProVerif header declarations.
-- Takes a literal rendering function and a term, returns the rendered
-- Doc and the set of headers needed for declarations (e.g., free constants).
renderTermWithHeaders :: (Show v) => (Lit Name v -> Doc) -> VTerm Name v -> (Doc, S.Set ProVerifHeader)
renderTermWithHeaders ppLit t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
      Lit v -> ppLit v
      FApp (AC (ACfct (f, _))) _ -> translationFail $ "User defined AC function " ++ show f ++ " not supported."
      FApp (AC Xor) ts -> ppXor ts
      FApp (AC o) ts -> ppTerms (ppACOp o) 1 "(" ")" ts
      FApp (NoEq s) [] | s == natOneSym -> text "1"
      FApp (NoEq s) [t1, t2] | s == expSym -> text "exp(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
      FApp (NoEq s) [t1, t2] | s == diffSym -> text "choice" <> text "[" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text "]"
      FApp (NoEq _) [t1, t2] | isPair tm -> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
      FApp (NoEq (f, _)) [] -> text $ ppFunSym f
      FApp (NoEq (f, _)) ts -> ppFun f ts
      FApp (C EMap) ts -> ppFun emapSymString ts
      FApp List ts -> ppFun (BC.pack "LIST") ts

    ppACOp Mult = "*"
    ppACOp NatPlus = "+"
    ppACOp Xor = "⊕"
    ppACOp u = translationFail $ "Unsupported operator " ++ show u

    ppXor [] = text "one"
    ppXor [t1, t2] = text "xor(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
    ppXor (t1 : ts) = text "xor(" <> ppTerm t1 <> text ", " <> ppXor ts <> text ")"
    ppTerms sepa n lead finish =
      fcat
        . (text lead :)
        . (++ [text finish])
        . map (nest n)
        . punctuate (text sepa)
        . map ppTerm
    ppFun f ts =
      text (ppFunSym f ++ "(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm tm = case viewTerm tm of
      Lit (Con (Name PubName n)) ->
        if show n `elem` ["g", "one", "zero"]
          then S.empty
          else -- The 's' is just prepended here instead of using sanitizeSymbol, because that function
          -- only does the prepending for reserved keywords and symbols starting with a digit. For
          -- free bitstrings however, we ALWAYS want the leading 's', to also avoid clashes with
          -- function names, rule names, event names etc. We could also do it like that for variables
          -- and function names (where we use sanitizeSymbol now), but I thought if we did it in all
          -- other places it might not be needed there, and I thought it would be better to leave as
          -- much as possible of the original naming as it is
            S.singleton (Sym "free" ("s" ++ show n) ":bitstring" [])
      Lit _ -> S.empty
      FApp _ ts -> foldl (\x y -> x `S.union` getHdTerm y) S.empty ts

-- | Render a SapicTerm, collecting the constants that need to be declared.
-- matchVars is the set of vars that correspond to pattern matching.
-- isPattern enables pattern match printing, which adds types to variables and = to constants.
renderSapicTermWithPattern :: TranslationContext -> S.Set LVar -> Bool -> SapicTerm -> (Doc, S.Set ProVerifHeader)
renderSapicTermWithPattern tc mVars isPattern = renderTermWithHeaders ppLit
  where
    ppLit v = case v of
      Con (Name FreshName n) -> text . sanitizeSymbol 'a' $ show n
      Con (Name PubName n) | isPattern -> text "=" <> text ("s" ++ show n)
      Con (Name PubName n) -> ppPubName n
      Var (SapicLVar lvar@(LVar _ lsort _) _)
        | lsort `elem` [LSortPub, LSortFresh, LSortNat] ->
            if isPattern || S.member lvar mVars
              then text "=" <> ppLVar lvar
              else ppLVar lvar
      Var (SapicLVar lvar _)
        | S.member lvar mVars -> text "=" <> ppLVar lvar
      l | isPattern -> ppTypeLit tc l
      Var (SapicLVar lvar _) -> ppLVar lvar
      l -> text . sanitizeSymbol 'a' $ show l

ppSapicTerm :: TranslationContext -> SapicTerm -> (Doc, S.Set ProVerifHeader)
ppSapicTerm tc = renderSapicTermWithPattern tc S.empty False

-- | Render an LNTerm, collecting the constants that need to be declared.
ppLNTerm :: TranslationContext -> LNTerm -> (Doc, S.Set ProVerifHeader)
ppLNTerm _ = renderTermWithHeaders ppLit
  where
    ppLit v = case v of
      Con (Name FreshName n) -> text . sanitizeSymbol 'a' $ show n
      Con (Name PubName n) -> ppPubName n
      Var lvar -> ppLVar lvar
      tm2 -> text . sanitizeSymbol 'a' $ show tm2

-- | Render a Fact, collecting the constants that need to be declared.
ppFact :: TranslationContext -> Fact SapicTerm -> (Doc, S.Set ProVerifHeader)
ppFact tc (Fact tag _ ts)
  | factTagArity tag /= length ts = renderFactWithName ("MALFORMED-" ++ show tag) ts
  | otherwise = renderFactWithName ('e' : factTagName tag) ts
  where
    renderFactWithName name ts2 =
      (nestShort' (name ++ "(") ")" . fsep . punctuate comma $ pts, sh)
      where
        (pts, shs) = unzip $ map (ppSapicTerm tc) ts2
        sh = S.unions shs

ppAction ::
  ProcessAnnotation LVar ->
  TranslationContext ->
  LSapicAction ->
  (Doc, S.Set ProVerifHeader, Bool)
ppAction ProcessAnnotation {isStateChannel = Nothing} tc (New v) =
  (text "new " <> ppTypeVar tc v, S.empty, True)
ppAction ProcessAnnotation {pureState = False, isStateChannel = Just t} tc (New v@(SapicLVar lvar _)) =
  ( extras $
      text "new "
        <> channel
        <> text "[assumeCell];"
        $$ text "new lock_"
        <> channel
        <> text "[assumeCell];"
        -- we also declare the corresponding lock channel, and initialize it
        $$ text "out(lock_"
        <> ppLVar lvar
        <> text ",0) |",
    if hasUnboundStates tc then sht else S.empty,
    False
  )
  where
    channel = ppTypeVar tc v
    (pt, sht) = ppSapicTerm tc t
    extras x =
      if hasUnboundStates tc
        then
          x
            $$ text "insert tbl_states_handle("
            <> pt
            <> text ", "
            <> ppLVar lvar
            <> text ");"
            $$ text "insert tbl_locks_handle("
            <> pt
            <> text ", lock_"
            <> ppLVar lvar
            <> text ");"
        else x
ppAction ProcessAnnotation {pureState = True, isStateChannel = Just _} tc (New v) =
  ( text "new " <> ppTypeVar tc v <> text "[assumeCell]",
    S.empty,
    True
  )
ppAction _ TranslationContext {trans} Rep | trans == ProVerif = (text "!", S.empty, False)
ppAction _ TranslationContext {trans = DeepSec} Rep = (text "", S.empty, False)
ppAction _ tc (ChIn t1 t2 mvars)
  | trans tc == ProVerif || isPlainVar t2 =
      ( text "in(" <> pt1 <> text "," <> pt2 <> text ")",
        sh1 `S.union` sh2,
        True
      )
  where
    isPlainVar (LIT (Var (SapicLVar _ _))) = True
    isPlainVar _ = False
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t2

-- pattern matching on input for deepsec is not supported
ppAction _ tc@TranslationContext {trans = DeepSec} (ChIn t1 t2 mvars) =
  ( text "in("
      <> pt1
      <> text ","
      <> text pt2var
      <> text ");"
      $$ text "let ("
      <> pt2
      <> text ")="
      <> text pt2var
      <> text " in",
    sh1 `S.union` sh2,
    False
  )
  where
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t2
    pt2var = "fresh" ++ stripNonAlphanumerical (render pt2)
ppAction _ tc (ChOut t1 t2) = (text "out(" <> pt1 <> text "," <> pt2 <> text ")", sh1 `S.union` sh2, True)
  where
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = ppSapicTerm tc t2
ppAction _ tc@TranslationContext {trans} (Event (Fact tag m ts)) | trans == ProVerif = (text "event " <> pa, sh, True) -- event Headers are definde globally inside loadHeaders
  where
    (pa, sh) = ppFact tc (Fact tag m ts)
ppAction _ TranslationContext {trans = DeepSec} (Event _) = (text "", S.empty, False)
-- For pure states, we do not put locks and unlocks
ppAction ProcessAnnotation {pureState = True} TranslationContext {trans} (Lock _)
  | trans == ProVerif =
      (text "", S.empty, False)
-- If there is a state channel, we simply use it
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} TranslationContext {trans} (Lock _)
  | trans == ProVerif =
      ( text "in(lock_" <> ppLVar lvar <> text "," <> text "counterlock" <> ppLVar lvar <> text ":nat)",
        S.empty,
        True
      )
-- If there is no state channel, we must use the table
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans} (Lock t)
  | trans == ProVerif =
      ( text "get tbl_locks_handle("
          <> pt
          <> text ","
          <> text ptvar
          <> text ") in"
          $$ text "in("
          <> text ptvar
          <> text " , counter"
          <> text ptvar
          <> text ":nat)",
        sh,
        True
      )
  where
    freevars = S.fromList $ map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = renderSapicTermWithPattern tc freevars True t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)
ppAction ProcessAnnotation {pureState = True} TranslationContext {trans} (Unlock _)
  | trans == ProVerif =
      (text "", S.empty, False)
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} TranslationContext {trans} (Unlock _)
  | trans == ProVerif =
      ( text "out(lock_" <> ppLVar lvar <> text "," <> text "counterlock" <> ppLVar lvar <> text "+1" <> text ") | ",
        S.empty,
        False
      )
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans} (Unlock t)
  | trans == ProVerif =
      (text "out(" <> text ptvar <> text " , counter" <> text ptvar <> text "+1) | ", sh, False)
  where
    (pt, sh) = ppSapicTerm tc t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = _} tc@TranslationContext {trans} (Insert _ c)
  | trans == ProVerif =
      ( text "out(" <> ppLVar lvar <> text ", " <> pc <> text ") |",
        shc,
        False
      )
  where
    (pc, shc) = ppSapicTerm tc c

-- Should never happen
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = True} TranslationContext {trans} (Insert _ _)
  | trans == ProVerif =
      translationInvariantFail "SAPIC invariant failed: a pure-state insert has no state channel."
-- must rely on the table
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans} (Insert t t2)
  | trans == ProVerif =
      ( text "in("
          <> text ptvar
          <> text ", "
          <> text dumpvar
          <> text ":bitstring);"
          $$ text "out("
          <> text ptvar
          <> text " , "
          <> pt2
          <> text ") | ",
        S.insert hd $ sh `S.union` sh2,
        False
      )
  where
    (pt, sh) = ppSapicTerm tc t
    (pt2, sh2) = ppSapicTerm tc t2
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    dumpvar = "dumpvar" ++ stripNonAlphanumerical (render pt)
    hd = Sym "free" ptvar ":channel" []
ppAction _ TranslationContext {trans = ProVerif} (MSR prems acts concs rests matchVars)
  | not (null rests) =
      translationFail "Embedded MSR constraints are currently not supported for ProVerif export."
  | otherwise =
      (msrDoc, msrHeaders, hasTailDocs)
  where
    lnPrems = map toLNFact prems
    lnActs = map toLNFact acts
    lnConcs = map toLNFact concs
    matched = S.map (show . toLVar) matchVars
    (msrDoc, msrHeaders, hasTailDocs) = translateEmbeddedRuleAction matched lnPrems lnActs lnConcs
ppAction _ _ _ = translationFail "Action not supported for translation"

ppSapic :: (LNFormula -> Doc) -> TranslationContext -> LProcess (ProcessAnnotation LVar) -> (Doc, S.Set ProVerifHeader)
ppSapic _ _ (ProcessNull _) = (text "0", S.empty) -- remove zeros when not needed
ppSapic renderFormula tc (ProcessComb Parallel _ pl pr) = (parens $ nest 2 (parens ppl) $$ text "|" $$ nest 2 (parens ppr), pshl `S.union` pshr)
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
    (ppr, pshr) = ppSapic renderFormula tc pr
ppSapic renderFormula tc (ProcessComb NDC _ pl pr) = (nest 4 (parens ppl) $$ text "+" <> nest 4 (parens ppr), pshl `S.union` pshr)
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
    (ppr, pshr) = ppSapic renderFormula tc pr
ppSapic renderFormula tc (ProcessComb (Let t1 t2 mvars) _ pl (ProcessNull _)) =
  ( text "let "
      <> pt1
      <> text "="
      <> pt2
      <> text " in"
      $$ ppl,
    S.unions [sh1, sh2, pshl]
  )
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
    (pt1, sh1) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic renderFormula tc (ProcessComb (Let t1 t2 mvars) _ pl pr) =
  ( text "let "
      <> pt1
      <> text "="
      <> pt2
      <> text " in"
      $$ ppl
      $$ text "else "
      <> ppr,
    S.unions [sh1, sh2, pshl, pshr]
  )
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
    (ppr, pshr) = ppSapic renderFormula tc pr
    (pt1, sh1) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t1
    (pt2, sh2) = ppSapicTerm tc t2

-- if the process call does not have any argument, we just inline
ppSapic renderFormula tc (ProcessAction (ProcessCall _ []) _ pl) = (ppl, pshl)
  where
    (ppl, pshl) = ppSapic renderFormula tc pl

-- if there are state or lock channels created by addStateChannels, we must inline
ppSapic renderFormula tc@TranslationContext {hasBoundStates = True} (ProcessAction (ProcessCall {}) _ pl) =
  (ppl, pshl)
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
ppSapic _ tc (ProcessAction (ProcessCall name ts) _ _) =
  ( text name <> parens (fsep (punctuate comma ppts)),
    S.unions shs
  )
  where
    pts = map (ppSapicTerm tc) ts
    (ppts, shs) = unzip pts
ppSapic renderFormula tc (ProcessComb (Cond a) _ pl pr) =
  addElseBranch (text "if " <> pa <> text " then" $$ nest 4 (parens ppl), sh `S.union` pshl)
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
    (pa, sh) = ppFact' a
    ppFact' (Ato (Syntactic (Pred (Fact (ProtoFact _ "Smaller" _) _ [v1, v2]))))
      | Lit (Var (Free vn1)) <- viewTerm v1,
        Lit (Var (Free vn2)) <- viewTerm v2 =
          (ppUnTypeVar vn1 <> text "<" <> ppUnTypeVar vn2, S.empty)
    ppFact' p =
      case expandFormula (predicates tc) (toLFormula p) of
        Left _ -> translationFail "Export does not support tamarin predicates in conditionnals."
        Right form -> (renderFormula form, S.empty)
    addElseBranch (d, s) = case pr of
      ProcessNull _ -> (d, s)
      _ ->
        let (ppr, pshr) = ppSapic renderFormula tc pr
         in (d $$ text "else" $$ nest 4 (parens ppr), s `S.union` pshr)
ppSapic renderFormula tc (ProcessComb (CondEq t1 t2) _ pl (ProcessNull _)) =
  ( text "let (=" <> pt1 <> text ")=" <> pt2 <> text " in " $$ nest 4 (parens ppl),
    S.unions [sh1, sh2, pshl]
  )
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
    (pt1, sh1) = ppSapicTerm tc t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic renderFormula tc (ProcessComb (CondEq t1 t2) _ pl pr) =
  ( text "let (=" <> pt1 <> text ")=" <> pt2 <> text " in " $$ nest 4 (parens ppl) $$ text "else" <> nest 4 (parens ppr),
    S.unions [sh1, sh2, pshl, pshr]
  )
  where
    (ppl, pshl) = ppSapic renderFormula tc pl
    (ppr, pshr) = ppSapic renderFormula tc pr
    (pt1, sh1) = ppSapicTerm tc t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic renderFormula tc (ProcessComb (Lookup _ c) ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = True} pl (ProcessNull _)) =
  ( text "in(" <> pt <> text ", " <> pc <> text ");" $$ ppl,
    pshl
  )
  where
    pt = ppLVar lvar
    pc = ppTypeVar tc c
    (ppl, pshl) = ppSapic renderFormula tc pl

ppSapic _ _ (ProcessComb (Lookup _ _) ProcessAnnotation {stateChannel = Nothing, pureState = True} _ (ProcessNull _)) =
  translationInvariantFail "SAPIC invariant failed: a pure-state lookup has no state channel."
ppSapic renderFormula tc (ProcessComb (Lookup _ c) ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} pl (ProcessNull _)) =
  ( text "in("
      <> pt
      <> text ", "
      <> pc
      <> text ");"
      $$ text "out("
      <> pt
      <> text ", "
      <> pc2
      <> text ") |"
      $$ ppl,
    pshl
  )
  where
    pt = ppLVar lvar
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    (ppl, pshl) = ppSapic renderFormula tc pl
ppSapic renderFormula tc (ProcessComb (Lookup t c) ProcessAnnotation {stateChannel = Nothing, pureState = False} pl (ProcessNull _)) =
  ( text "get tbl_states_handle("
      <> pt
      <> text ","
      <> text ptvar
      <> text ") in"
      $$ text "in("
      <> text ptvar
      <> text " , "
      <> pc
      <> text ");"
      $$ text "out("
      <> text ptvar
      <> text " , "
      <> pc2
      <> text ") |"
      $$ ppl,
    sh `S.union` pshl
  )
  where
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    freevars = S.fromList $ map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = renderSapicTermWithPattern tc freevars True t
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    (ppl, pshl) = ppSapic renderFormula tc pl
ppSapic renderFormula tc (ProcessComb (Lookup t c) ProcessAnnotation {stateChannel = Nothing, pureState = False} pl pr) =
  ( text "get tbl_states_handle("
      <> pt
      <> text ","
      <> text ptvar
      <> text ") in"
      $$ nest
        4
        ( parens
            ( text "in("
                <> text ptvar
                <> text " , "
                <> pc
                <> text ");"
                $$ text "out("
                <> text ptvar
                <> text " , "
                <> pc2
                <> text ") | "
                $$ ppl
            )
        )
      $$ text "else"
      $$ nest
        4
        ( parens
            ( text "new "
                <> text ptvar
                <> text ":channel [assumeCell];" -- the cell did not exists, we create it !
                $$ text "insert tbl_states_handle("
                <> pt'
                <> text ", "
                <> text ptvar
                <> text ");"
                $$ text "out("
                <> text ptvar
                <> text ",0) |"
                $$ ppr
            )
        ),
    S.unions [sh, pshl, pshr]
  )
  where
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    freevars = S.fromList $ map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = renderSapicTermWithPattern tc freevars True t
    (pt', _) = ppSapicTerm tc t
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    (ppl, pshl) = ppSapic renderFormula tc pl
    (ppr, pshr) = ppSapic renderFormula tc pr
ppSapic _ _ (ProcessComb (Lookup _ _) _ _ _) =
  translationFail "The export does not support a lookup with an else branch."
ppSapic renderFormula tc@TranslationContext {trans} (ProcessAction Rep _ p) | trans == ProVerif = (text "!" $$ parens pp, psh)
  where
    (pp, psh) = ppSapic renderFormula tc p
ppSapic renderFormula tc@TranslationContext {trans = DeepSec} (ProcessAction Rep _ p) =
  ( text ("!^" ++ show (replicationBound tc)) <> parens pp,
    psh
  )
  where
    (pp, psh) = ppSapic renderFormula tc p
ppSapic _ tc (ProcessAction a an (ProcessNull _)) =
  if unNeedZero
    then (pa, sh)
    else (pa <> text "0", sh)
  where
    (pa, sh, unNeedZero) = ppAction an tc a
ppSapic renderFormula tc (ProcessAction a an p) =
  if needSep
    then (pa <> text ";" $$ pp, sh `S.union` psh)
    else (pa $$ pp, sh `S.union` psh)
  where
    (pa, sh, needSep) = ppAction an tc a
    (pp, psh) = ppSapic renderFormula tc p

addAttackerReportProc :: (LNFormula -> Doc) -> TranslationContext -> OpenTheory -> Doc -> Doc
addAttackerReportProc renderFormula tc thy p =
  text "(" $$ p $$ text ")| in(" <> att <> text ",(x:bitstring,y:bitstring)); if " <> formula <> text " then out(" <> att <> text ", rep(x,y))"
  where
    att = fst $ getAttackerChannel tc Nothing
    reportPreds =
      List.find (\(Predicate (Fact tag _ _) _) -> showFactTag tag == "Report") $
        theoryPredicates thy
    formula = case reportPreds of
      Nothing -> translationFail "Translation Error, the Report predicate must be defined."
      Just (Predicate _ form) -> renderFormula form

------------------------------------------------------------------------------
-- Main printer for processes
------------------------------------------------------------------------------

-- | Annotate and render one top-level process together with its attacker
-- context, returning the extended context, the rendered process, the
-- collected headers, and the (bound, unbound) state usage.
loadSingleProc :: (LNFormula -> Doc) -> TranslationContext -> OpenTheory -> PlainProcess -> (TranslationContext, Doc, S.Set ProVerifHeader, (Bool, Bool))
loadSingleProc renderFormula tc thy pr =
  let (d, headers) = ppSapic renderFormula tc2 p
   in (tc2, d, S.union hd headers, hasStates)
  where
    p = makeAnnotations thy pr
    hasStates = hasBoundUnboundStates p
    (tc2, hd) = mkAttackerContext tc {hasBoundStates = fst hasStates, hasUnboundStates = snd hasStates} p

loadProc :: (LNFormula -> Doc) -> TranslationContext -> OpenTheory -> (Doc, S.Set ProVerifHeader, Bool, Bool)
loadProc renderFormula tc thy = case theoryProcesses thy of
  [] -> (text "", S.empty, False, False)
  [pr] ->
    let (tc2, d, headers, hasStates) = loadSingleProc renderFormula tc thy pr
        finald
          | isNothing (List.find (== "locations-report") (theoryBuiltins thy)) = d
          | otherwise = addAttackerReportProc renderFormula tc2 thy d
     in (finald, headers, fst hasStates, snd hasStates)
  _ -> translationFail "Multiple sapic processes were defined."

-- | Set up the attacker channel if it does not already exist.
ensureAttackerContext ::
  TranslationContext ->
  LProcess (ProcessAnnotation LVar) ->
  (TranslationContext, S.Set ProVerifHeader)
ensureAttackerContext tc proc = case attackerChannel tc of
  Nothing -> mkAttackerContext tc proc
  Just _ -> (tc, S.empty)

-- | Render the theory's formal comments as target comments.
formalCommentDocs :: OpenTheory -> [Doc]
formalCommentDocs thy =
  [text "(*" $$ text body $$ text "*)" | (_, body) <- theoryFormalComments thy]

loadMacroProc :: (LNFormula -> Doc) -> TranslationContext -> OpenTheory -> ([Doc], S.Set ProVerifHeader)
loadMacroProc renderFormula tc thy = loadMacroProcs renderFormula tc thy (theoryProcessDefs thy)

loadMacroProcs :: (LNFormula -> Doc) -> TranslationContext -> OpenTheory -> [ProcessDef] -> ([Doc], S.Set ProVerifHeader)
loadMacroProcs _ _ _ [] = ([text ""], S.empty)
loadMacroProcs renderFormula tc thy (p : q) =
  let (docs, heads) = loadMacroProcs renderFormula tc3 thy q
   in case p._pVars of
        -- TODO bugfix, this is probably wrong when the macro does not have any parameter
        Nothing -> (docs, hd `S.union` heads)
        Just pvars ->
          let (newText, newHeads) = ppSapic renderFormula tc3 mainProc
              vrs = text "(" <> fsep (punctuate comma (map (ppTypeVar tc3) pvars)) <> text ")"
              headers = headersOfType $ map extractType pvars
              macroDef =
                text "let "
                  <> text p._pName
                  <> vrs
                  <> text "="
                  $$ nest 4 newText
                  <> text "."
           in (macroDef : docs, hd `S.union` newHeads `S.union` heads `S.union` headers)
  where
    mainProc = makeAnnotations thy p._pBody
    extractType (SapicLVar _ ty) = ty
    hasStates = hasBoundUnboundStates mainProc
    (tc2, hd) = ensureAttackerContext tc mainProc
    tc3 = tc2 {hasBoundStates = fst hasStates, hasUnboundStates = snd hasStates}

loadDiffProc :: (LNFormula -> Doc) -> TranslationContext -> OpenTheory -> ([Doc], S.Set ProVerifHeader, Bool, Bool)
loadDiffProc renderFormula tc thy = case theoryDiffEquivLemmas thy of
  [] -> ([], S.empty, False, False)
  [pr] ->
    let (_, d, headers, hasStates) = loadSingleProc renderFormula tc thy pr
     in ([text "process" $$ nest 4 d], headers, fst hasStates, snd hasStates)
  _ -> translationFail "Multiple sapic processes were defined."

loadEquivProc :: (LNFormula -> Doc) -> TranslationContext -> OpenTheory -> ([Doc], S.Set ProVerifHeader, Bool, Bool)
loadEquivProc renderFormula tc thy = loadEquivProcs renderFormula tc thy (theoryEquivLemmas thy)

loadEquivProcs ::
  (LNFormula -> Doc) ->
  TranslationContext ->
  OpenTheory ->
  [(PlainProcess, PlainProcess)] ->
  ([Doc], S.Set ProVerifHeader, Bool, Bool)
loadEquivProcs _ _ _ [] = ([], S.empty, False, False)
loadEquivProcs renderFormula tc thy ((p1, p2) : q) =
  let (docs, heads, hadBoundStates, hadUnboundStates) = loadEquivProcs renderFormula tc3 thy q
      (newText1, newHeads1) = ppSapic renderFormula tc3 mainProc1
      (newText2, newHeads2) = ppSapic renderFormula tc3 mainProc2
      macroDef = case trans tc of
        ProVerif ->
          text "equivalence"
            $$ nest 4 newText1
            $$ nest 4 newText2
        DeepSec ->
          text "query session_equiv("
            $$ nest 4 newText1
            <> text ","
            $$ nest 4 newText2
            <> text ")."
   in ( macroDef : docs,
        S.unions [hd, newHeads1, newHeads2, heads],
        hasBoundSt || hadBoundStates,
        hasUnboundSt || hadUnboundStates
      )
  where
    mainProc1 = makeAnnotations thy p1
    mainProc2 = makeAnnotations thy p2
    hasStates1 = hasBoundUnboundStates mainProc1
    hasStates2 = hasBoundUnboundStates mainProc2
    hasBoundSt = fst hasStates1 || fst hasStates2
    hasUnboundSt = snd hasStates1 || snd hasStates2
    (tc2, hd) = ensureAttackerContext tc mainProc2
    tc3 = tc2 {hasBoundStates = hasBoundSt, hasUnboundStates = snd hasStates1 || snd hasStates2}

headersOfType :: [SapicType] -> S.Set ProVerifHeader
headersOfType types =
  S.fromList $
    foldl
      ( \y x -> case x of
          Nothing -> y
          Just s -> Type s : y
      )
      []
      types

headerOfFunSym :: SapicFunSym -> S.Set ProVerifHeader
headerOfFunSym (NoEqUser (f, (k, pub, Constructor, _)), inTypes, outType) =
  Fun "fun" (ppFunSym f) k ("(" ++ makeArgtypes inTypes ++ "):" ++ ppType outType) (priv_or_pub pub) `S.insert` headersOfType (outType : inTypes)
  where
    priv_or_pub Public = []
    priv_or_pub Private = ["private"]
headerOfFunSym (ACfctUser f, _, _) = translationFail $ "User defined AC function " ++ show f ++ "not supported."-- "AC function not supported"
headerOfFunSym _ = S.empty

-- | Load headers from an OpenTheory into a set of ProVerif Headers
loadHeaders :: S.Set String -> TranslationContext -> OpenTheory -> TypingEnvironment -> IO (S.Set ProVerifHeader)
loadHeaders ruleIdEvents tc thy typeEnv = do
  eqHeaders <- foldMap (headersOfRule tc typeEnv) sigRules
  pure $
    typedHeaderOfFunSym
      `S.union` headerBuiltins'
      `S.union` eqHeaders
      `S.union` eventHeaders
  where
    sig = thy._thySignature._sigMaudeInfo
    builtins' x = case builtins x of
      AccurateBuiltin y -> y
      BestEffortBuiltin y -> y
      NotSupportedBuiltin s -> translationFail s
    -- all builtins are contained in Sapic Element
    headerBuiltins = S.fromList $ foldMap builtins' (theoryBuiltins thy)

    -- builtin headers need to be filtered, to make sure we don't redefine a user-defined function
    headerBuiltins' = S.filter keep headerBuiltins
      where
        funNames = S.fromList [n | Fun _ n _ _ _ <- S.toList typedHeaderOfFunSym]
        keep (Fun _ n _ _ _) = n `S.notMember` funNames
        -- Models define g/0 themselves even when using the diffi-hellman builtin.
        -- FIXME: Given builtins higher precedence than user defined functions seems more intuitive.
        keep (Sym _ n _ _) = n `S.notMember` funNames
        keep _ = True

    -- all user declared function symbols have typinginfos
    userDeclaredFunctions = theoryFunctionTypingInfos thy
    typedHeaderOfFunSym = foldMap headerOfFunSym userDeclaredFunctions

    -- events headers
    eventHeaders =
      M.foldrWithKey
        ( \tag types acc ->
            let factName = factTagName tag
                adjustedTypes =
                  if factName `S.member` ruleIdEvents
                    then Nothing : types
                    else types
            in HEvent ('e' : factName) ("(" ++ makeArgtypes adjustedTypes ++ ")") `S.insert` acc
        )
        S.empty
        typeEnv.events
    -- generating headers for equations
    sigRules = S.toList (stRules sig)

toSapicLVar :: LVar -> SapicLVar
toSapicLVar v = SapicLVar v Nothing

toSapicTerm :: LNTerm -> SapicTerm
toSapicTerm = fmap f
  where
    f (Con c) = Con c
    f (Var v) = Var $ toSapicLVar v

headersOfRule :: TranslationContext -> TypingEnvironment -> CtxtStRule -> IO (S.Set ProVerifHeader)
headersOfRule tc typeEnv r | (lhs `RRule` rhs) <- ctxtStRuleToRRule r = do
  tye <- typeTermsWithEnv typeEnv (map toSapicTerm [lhs, rhs])
  let (plhs, lsh) = ppLNTerm tc lhs
      (prhs, rsh) = ppLNTerm tc rhs
      prefix = case viewTerm lhs of
        FApp (NoEq (_, (_, _, Destructor, _))) _ -> "reduc"
        _ -> "equation"
      suffix = case viewTerm lhs of
        FApp (NoEq (_, (_, Private, Destructor, _))) _ -> " [private]"
        _ -> ""
      freesr = frees lhs `union` frees rhs
      freesrTyped = map (\v -> (v, M.lookup v tye.vars)) freesr
      hrule =
        Eq
          prefix
          ( case map ppFreeTyped freesrTyped of
              [] -> ""
              xs ->
                "forall "
                  ++ render (fsep (punctuate comma xs))
                  ++ ";"
          )
          (render (plhs <-> text "=" <-> prhs))
          suffix

  pure $ S.unions [S.singleton hrule, lsh, rsh]
  where
    ppFreeTyped (v, Nothing) = ppLVar v <> text ":bitstring"
    ppFreeTyped (v, Just s) = ppLVar v <> text ":" <> text (ppType s)

attChanName :: String
attChanName = "att"

mkAttackerChannel ::
  (MonadFresh m) =>
  LProcess (ProcessAnnotation LVar) ->
  m LVar
mkAttackerChannel _ = freshLVar attChanName LSortMsg

mkAttackerContext ::
  TranslationContext ->
  LProcess (ProcessAnnotation LVar) ->
  (TranslationContext, S.Set ProVerifHeader)
mkAttackerContext tc p =
  (tc {attackerChannel = Just attackerVar}, S.singleton hd)
  where
    attackerVar@(LVar n _ _) = evalFresh (mkAttackerChannel p) initStateAtt
    initState = avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $ S.toList $ varsProc p
    initStateAtt = fromMaybe 0 (M.lookup attChanName initState)
    hd = Sym "free" n ":channel" []

-- given an optional channel name and a translation context, returns the corresponding printer
getAttackerChannel ::
  TranslationContext ->
  Maybe SapicTerm ->
  (Doc, S.Set ProVerifHeader)
getAttackerChannel tc t1 = case (t1, attackerChannel tc) of
  (Just tt1, _) -> ppSapicTerm tc tt1
  (Nothing, Just (LVar n _ _)) -> (text n, S.empty)
  _ -> translationInvariantFail "SAPIC invariant failed: the implicit attacker channel was not allocated."

------------------------------------------------------------------------------
-- Some utility functions
------------------------------------------------------------------------------

makeArgtypes :: [SapicType] -> String
makeArgtypes [] = ""
makeArgtypes [x] = ppType x
makeArgtypes (x : t) = ppType x ++ "," ++ makeArgtypes t

-- return the annotated process
makeAnnotations :: OpenTheory -> PlainProcess -> LProcess (ProcessAnnotation LVar)
makeAnnotations thy p = res
  where
    p' = report $ toAnProcess p
    res = annotatePureStates p'
    report pr =
      if isNothing (List.find (== "locations-report") (theoryBuiltins thy))
        then pr
        else translateTermsReport pr
