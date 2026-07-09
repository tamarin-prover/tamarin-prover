{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
module Theory.Tools.IntruderRules (
    subtermConstructorRules
  , destructionRulesAC
  , destructionRulesNoEq
  , dhIntruderRules
  , bpIntruderRules
  , xorIntruderRules
  , multisetIntruderRules
  , mkDUnionRule
  , specialIntruderRules
  , natIntruderRules
  , variantsIntruder

  , builtInDestrRule
  , builtInDestrRuleInclPair

  -- ** Classifiers
  , isDExpRule
  , isDEMapRule
  , isDPMultRule
  , isNDCRule
  , isNDCDiffRule
  ) where

import           Control.Basics hiding (empty)
import           Control.Monad.Reader

import           Data.List hiding (isSuffixOf)
import qualified Data.Set                          as S
import           Data.ByteString.Char8 (ByteString, append, pack, empty, isSuffixOf)

import           Extension.Data.Label

import           Term.Maude.Signature
import           Term.Narrowing.Variants.Compute
import           Term.Rewriting.Norm
import           Term.SubtermRule
import           Term.Subsumption
import           Term.Positions

import           Theory.Model


-- Variants of intruder deduction rules
----------------------------------------------------------------------


------------------------------------------------------------------------------
-- Special Intruder rules
------------------------------------------------------------------------------

{-
These are the special intruder that are always included.

rule coerce:
   [ KD( x ) ] --[ KU( x ) ]-> [ KU( x ) ]

rule pub:
   [ ] --[ KU( $x ) ]-> [ KU( $x ) ]
   
rule gen_fresh:
   [ Fr( ~x ) ] --[ KU( ~x ) ]-> [ KU( ~x ) ]

rule isend:
   [ KU( x) ] --[ K( x ) ]-> [ In( x ) ]

rule irecv:
   [ Out( x) ] --> [ KD( x ) ]

rule iequality:
   [ KU( x ) , KD( x ) ] --> []

-}
-- | @specialIntruderRules@ returns the special intruder rules that are
--   included independently of the message theory
specialIntruderRules :: Bool -> [IntrRuleAC]
specialIntruderRules diff =
    [ kuRule CoerceRule      [kdFact x_var]                 (x_var)         []
    , kuRule PubConstrRule   []                             (x_pub_var)     [(x_pub_var)]
    , kuRule FreshConstrRule [freshFact x_fresh_var] (x_fresh_var)          []
    , Rule ISendRule [kuFact x_var]  [inFact x_var] [kLogFact x_var]        []
    , Rule IRecvRule [outFact x_var] [kdFact x_var] []                      []
    ] ++
    ([Rule IEqualityRule [kuFact x_var, kdFact x_var]  [] [] [] | diff])
  where
    kuRule name prems t nvs = Rule name prems [kuFact t] [kuFact t] nvs

    x_var       = varTerm (LVar "x"  LSortMsg   0)
    x_pub_var   = varTerm (LVar "x"  LSortPub   0)
    x_fresh_var = varTerm (LVar "x"  LSortFresh 0)


------------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------------

{-
When using the natural-numbers plugin, the following rule is included.

rule nat:
   [ ] --[ KU( x:nat ) ]-> [ KU( x:nat ) ]

-}

-- | @natIntruderRules@ returns the natural numbers constructor
natIntruderRules :: [IntrRuleAC]
natIntruderRules =
    [ kuRule NatConstrRule [] x_nat_var [x_nat_var] ]
  where
    kuRule name prems t nvs = Rule name prems [kuFact t] [kuFact t] nvs

    x_nat_var   = varTerm (LVar "x"  LSortNat   0)

------------------------------------------------------------------------------
-- Subterm Intruder theory
------------------------------------------------------------------------------

-- | @destuctionRules diff st@ returns the destruction rules for the given
-- context subterm rule @st@
destructionRules :: Bool -> CtxtStRule -> [IntrRuleAC]
destructionRules bool (CtxtStRule lhs@(viewTerm -> FApp _ _) (StRhs (pos:[]) rhs)) | bool || (frees rhs /= []) || containsPrivate rhs =
    go [] lhs pos [] []
  where
    go _      _                       []     _ _                     = []
    -- term already in premises, but necessary for constant conclusions
    go _      (viewTerm -> FApp _ _)  (_:[]) _ _ | frees rhs /= [] = []
    go uprems (viewTerm -> FApp fun@(NoEq (_,(_,Public,_,_))) as) (i:p) n pd = irule uprems as i pd n fun ++ go (uprems' uprems as i) (t' as i) p (funs n fun) (posname i pd)
    go uprems (viewTerm -> FApp fun@(AC (ACfct (_,(Public,_,_)))) as) (i:p) n pd = irule uprems as i pd n fun ++ go (uprems' uprems as i) (t' as i) p (funs n fun) (posname i pd)
    go _      (viewTerm -> FApp (NoEq (_,(_,Private,_,_))) _) _     _ _  = []
    go _      (viewTerm -> FApp (AC (ACfct (_,(Private,_,_)))) _) _     _ _  = []
    go _      (viewTerm -> Lit _)                         (_:_) _ _  =
        error "IntruderRules.destructionRules: impossible, position invalid"
    go _      _                       _     _ _                     = []

    uprems' uprems as i = uprems++[ t | (j, t) <- zip [0..] as, i /= j ]
    t' as i             = as!!i
    funs n fun          = n ++ [fun]
    posname i pd        = "_" ++ show i ++ pd
    name i pd n fun     = append (pack (posname i pd)) (foldl append empty (map (\x -> append (pack "_") (pack $ showFunSymName x)) (funs n fun))) -- append (pack (posname i pd)) (funs n f)
    irule uprems as i pd n fun = if  (t' as i /= rhs && rhs `notElem` (uprems' uprems as i))
              then [ Rule (DestrRule (name i pd n fun) (-1) (rhs == lhs `atPos` pos) (frees rhs == []) (funs n fun))
                          ((kdFact  (t' as i)):(map kuFact (uprems' uprems as i)))
                          [kdFact rhs] [] [] ]
              else []

destructionRules bool (CtxtStRule lhs (StRhs (pos:posit) rhs))
    | bool || (frees rhs /= []) || containsPrivate rhs =
      destructionRules bool (CtxtStRule lhs (StRhs [pos] rhs))
           ++ destructionRules bool (CtxtStRule lhs (StRhs posit rhs))
destructionRules _ _ = []

-- returns all equations with private constructors on the RHS
privateConstructorEquations :: [CtxtStRule] -> [(LNTerm, FunSym)]
privateConstructorEquations rs = case rs of
    []    -> []
    (CtxtStRule lhs (StRhs _ (viewTerm -> FApp fun@(NoEq (vname,(0,Private,_,_))) _))):xs
          -> (lhs, fun):(privateConstructorEquations xs)
    _:xs  -> privateConstructorEquations xs
    
-- given equations with private constructors on the RHS and a list of private function names x,
-- returns the list of all such constructors such that the LHS only contains public functions or functions in x
derivablePrivateConstants :: [(LNTerm, FunSym)] -> [FunSym] -> [FunSym]
derivablePrivateConstants eqs except =
    if any (containsNoPrivateExcept except . fst) eqs
        then
            derivablePrivateConstants (filter (\(l, _) -> not $ containsNoPrivateExcept except l) eqs) (except ++ map snd (filter (\(l,  _) -> containsNoPrivateExcept except l) eqs)) 
        else
            except

-- | @privateConstructorRules st@ returns the constructor rules for private constants that are consequences of rewrite rules in @st@
privateConstructorRules :: [CtxtStRule] -> [IntrRuleAC]
privateConstructorRules rules = map createRule $ derivablePrivateConstants (privateConstructorEquations rules) []
  where
    -- creates a constructor rule for constant s
    createRule f@(NoEq (s, _)) = Rule (ConstrRule (append (pack "_") s) f) [] [concfact] [concfact] []
      where m         = fApp f []
            concfact  = kuFact m

-- | Simple removal of subsumed rules for auto-generated subterm intruder rules.
minimizeIntruderRules :: Bool -> MaudeHandle -> [IntrRuleAC] -> [IntrRuleAC]
minimizeIntruderRules diff hnd rules =
    filter (not . isDoublePremiseRule)
      $ go [] rules
  where
    go checked [] = reverse checked
    go checked (r:unchecked) = go checked' unchecked
      where
        checked' = if any (\r' -> (equalDuplicateRuleUpToRenaming r r' `runReader` hnd) || ((not diff) && equalSubsetRuleUpToRenaming r r' `runReader` hnd))
                          (checked++unchecked)
                   then checked
                   else r:checked

    -- We assume that the KD-Fact is the first fact, which is the case in destructionRules above
    isDoublePremiseRule (Rule _ ((Fact KDFact _ [t]):prems) concs _ _) =
       null (frees concs)
         && not (any containsPrivate (t : concatMap getFactTerms prems))
         && isMsgVar t && elem (kuFact t) prems
    isDoublePremiseRule _                                               = False

-- | @subtermConstructorRules diff maudeSig@ returns the set of constructor rules for
--   the subterm (not Xor, DH, and MSet) part of the given signature.
subtermConstructorRules :: Bool -> MaudeHandle -> MaudeSig -> [IntrRuleAC]
subtermConstructorRules diff hnd maudeSig =
    minimizeIntruderRules diff hnd (constructionRules (userDefinedSTFunSyms maudeSig) ++ privateConstructorRules (S.toList $ stRules maudeSig))

-- | @constructionRules fSig@ returns the construction rules for the given
-- function signature @fSig@
constructionRules :: UserDefinedSig -> [IntrRuleAC]
constructionRules fSig =
    [ createRuleNoEq s f k | NoEqUser f@(s,(k,Public,Constructor,_)) <- S.toList fSig ] ++
    [ createRuleAC s f | ACfctUser f@(s,(Public,Constructor,_)) <- S.toList fSig ]
  where
    createRuleNoEq s f k = Rule (ConstrRule (append (pack "_") s) (NoEq f)) (map kuFact (vars k)) [concfactNoEQ f k] [concfactNoEQ f k] []
    createRuleAC s f = Rule (ConstrRule (append (pack "_") s) (AC (ACfct f))) (map kuFact (vars 2)) [concfactAC f] [concfactAC f] []
    vars k   = take k [ varTerm (LVar "x"  LSortMsg i) | i <- [0..] ]
    m f k    = fAppNoEq f (vars k)
    mAC f    = fAppACfct f (vars 2)
    concfactNoEQ f k = kuFact (m f k)
    concfactAC f = kuFact (mAC f)

destructionRulesAC :: Bool -> ACfctFunSig -> WithMaude [IntrRuleAC]
destructionRulesAC diff fSig = reader $ \hnd -> minimizeIntruderRules diff hnd $
    concatMap (decomposeNotSubterm diff . variantsIntruderAux hnd id True diff) [ (AC (ACfct f),createRule s f) | f@(s,(Public,_,_)) <- S.toList fSig, s `notElem` builtInDestrRule ]
  where
    createRule s f = Rule (DestrRule (append (pack "_") s) (-1) True True [AC (ACfct f)]) [kdFact (varTerm (LVar "x"  LSortMsg 0)), kuFact (varTerm (LVar "x"  LSortMsg 1))] [concfact] [concfact] []
      where vars     = take 2 [ varTerm (LVar "x"  LSortMsg i) | i <- [0..] ]
            mAC      = fAppACfct f vars
            concfact = kdFact mAC

    variantsIntruderAux hnd fun b d (f,r) = (f,variantsIntruder hnd fun b d r)

decomposeNotSubterm :: Bool -> (FunSym,[IntrRuleAC]) -> [IntrRuleAC]
decomposeNotSubterm bool (f,((Rule (DestrRule _ _ _ _ _) ((Fact KDFact _ (lhs:_)):other_prems) [(Fact KDFact _ [tc])] _ _):rq)) =
  case contextR of
    Just context -> destructionRules bool context ++ decomposeNotSubterm bool (f,rq)
    Nothing -> decomposeNotSubterm bool (f,rq)

  where
    contextR = rRuleToCtxtStRule (flhs `RRule` tc)
    flhs = FAPP f (lhs:(foldMap getFactTerms other_prems))
decomposeNotSubterm _ (_,[]) = []

-- | @destructionRulesNoEq diff fSig@ returns the destruction rules for the given
-- function signature @fSig@ (not AC cases)
destructionRulesNoEq :: Bool -> NoEqFunSig -> WithMaude [IntrRuleAC]
destructionRulesNoEq diff fSig = reader $ \hnd -> map (maxApplications hnd) . minimizeIntruderRules diff hnd $
    concatMap (decomposeNotSubterm diff . variantsIntruderAux hnd id True diff) [ (NoEq f,createRule s f k) | f@(s,(k,Public,_,_)) <- S.toList fSig, s `notElem` builtInDestrRule ]
  where
    createRule s f k | k /= 0 = Rule (DestrRule (append (pack "_") s) (-1) True True [NoEq f]) ((kdFact (varTerm (LVar "x"  LSortMsg (toInteger (k-1))))):(take (k-1) (map kuFact vars))) [concfact] [concfact] []
    -- the two boolean are set by default to True : it's computed juste after
      where vars     = take k [ varTerm (LVar "x"  LSortMsg i) | i <- [0..] ]
            m        = fAppNoEq f (reverse vars)
            concfact = kdFact m
    createRule s f 0 = Rule (DestrRule (append (pack "_") s) (-1) True True [NoEq f]) [] [concfact] [concfact] []
      where m        = fAppNoEq f []
            concfact = kdFact m

    variantsIntruderAux hnd fun b d (f,r) = (f,variantsIntruder hnd fun b d r)

-- | Compute maximum number of consecutive applications, implements N12
maxApplications :: MaudeHandle -> IntrRuleAC -> IntrRuleAC
maxApplications hnd (Rule (DestrRule name (-1) subterm constant funs) prems@((Fact KDFact _ [t]):_) concs@[Fact KDFact _ [rhs]] acts nvs) =
   Rule (DestrRule name (if containsOnlyNoEq rhs && containsOnlyNoEq t && runMaude (unifiableLNTerms rhs t)
                  then length (positions t) - (if isPrivateFunction t then 1 else 2)
                    -- We do not need to count t itself, hence - 1.
                    -- If t is a private function symbol we need to permit one more rule
                    -- application as there is no associated constructor.
                  else 0) subterm constant funs) prems concs acts nvs
        where
           runMaude = (`runReader` hnd)
maxApplications _ ir@(Rule (DestrRule name _ _ _ _) _ _ _ _) | any (`isSuffixOf`name) builtInDestrRuleInclPair = ir
maxApplications _ (Rule (DestrRule _ _ False _ _) _ _ _ _)   = error "maxApplications: This case should not happen, please report it on the github page"
maxApplications _ ir                                         = ir

------------------------------------------------------------------------------
-- Diffie-Hellman Intruder Rules
------------------------------------------------------------------------------

-- | @dhIntruderRules@ computes the intruder rules for DH
dhIntruderRules :: Bool -> WithMaude [IntrRuleAC]
dhIntruderRules diff = reader $ \hnd -> minimizeIntruderRules diff hnd $
    [ expRule  (ConstrRule (append (pack "_") expSymString) (NoEq expSym))  kuFact return
    , invRule  (ConstrRule (append (pack "_") invSymString) (NoEq invSym))  kuFact return
    -- The constructors for one and mult are only necessary in diff mode.
    -- They are never applied in trace mode as all corresponding constraints are solved directly,
    -- but they  will show up in the message theory, which is reassuring for users.
    , dhNeutralRule   (ConstrRule (append (pack "_") dhNeutralSymString) (NoEq dhNeutralSym))   kuFact return
    , oneRule  (ConstrRule (append (pack "_") oneSymString) (NoEq oneSym))  kuFact return
    , multRule (ConstrRule (append (pack "_") multSymString) (AC Mult)) kuFact return
    ] ++
    concatMap (variantsIntruder hnd id True diff)
      [ expRule (DestrRule (append (pack "_") expSymString) 0 True False [NoEq expSym]) kdFact (const [])
      , invRule (DestrRule (append (pack "_") invSymString) 0 True False [NoEq invSym]) kdFact (const [])
      ]
  where
    x_var_0 = varTerm (LVar "x" LSortMsg 0)
    x_var_1 = varTerm (LVar "x" LSortMsg 1)

    expRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact) []
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppExp (x_var_0, x_var_1)
        concfact = kudFact conc

    multRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact) []
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppAC Mult [x_var_0, x_var_1]
        concfact = kudFact conc

    invRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact] [concfact] (mkAction concfact) []
      where
        bfact    = kudFact x_var_0
        conc     = fAppInv x_var_0
        concfact = kudFact conc

    oneRule mkInfo kudFact mkAction =
        Rule mkInfo [] [concfact] (mkAction concfact) []
      where
        conc     = fAppNoEq oneSym []
        concfact = kudFact conc

    dhNeutralRule mkInfo kudFact mkAction =
        Rule mkInfo [] [concfact] (mkAction concfact) []
      where
        conc     = fAppNoEq dhNeutralSym []
        concfact = kudFact conc


-- | @variantsIntruder mh irule@ computes the deconstruction-variants
-- of a given intruder rule @irule@
variantsIntruder :: MaudeHandle -> ([LNSubstVFresh] -> [LNSubstVFresh]) -> Bool -> Bool -> IntrRuleAC -> [IntrRuleAC]
variantsIntruder hnd minimizeVariants applyFilters diff ru = go [] $ reverse $ do
    let ruleTerms = concatMap factTerms
                              (get rPrems ru++get rConcs ru++get rActs ru)
    fsigma <- minimizeVariants $ computeVariants (fAppList ruleTerms) `runReader` hnd
    let sigma     = freshToFree fsigma `evalFreshAvoiding` ruleTerms
        ruvariant = normRule' (apply sigma ru) `runReader` hnd
    guard (not applyFilters || (frees (get rConcs ruvariant) /= [] || diff) &&
           -- ground terms are already deducible by applying construction rules
           (not applyFilters || ruvariant /= ru) &&
           -- this is a construction rule
           (get rConcs ruvariant) \\ (get rPrems ruvariant) /= []
           -- The conclusion is included in the premises
           )

    case concatMap factTerms $ get rConcs ruvariant of
        [viewTerm -> FApp (AC Mult) _] ->
            fail "Rules with product conclusion are redundant"
        _                              -> return ruvariant
  where
    go checked [] = checked
    go checked (r:unchecked) = go checked' unchecked
      where
        checked' = if any (\r' -> equalRuleUpToRenaming r r' `runReader` hnd)
                          (checked++unchecked)
                   then checked
                   else r:checked

-- | @normRule irule@ computes the normal form of @irule@
normRule' :: IntrRuleAC -> WithMaude IntrRuleAC
normRule' (Rule i ps cs as nvs) = reader $ \hnd ->
    let normFactTerms = map (fmap (\t -> norm' t `runReader` hnd)) in
    let normTerms     = map (\t -> norm' t `runReader` hnd) in
    Rule i (normFactTerms ps) (normFactTerms cs) (normFactTerms as) (normTerms nvs)

------------------------------------------------------------------------------
-- Multiset intruder rules
------------------------------------------------------------------------------

multisetIntruderRules ::  [IntrRuleAC]
multisetIntruderRules = [mkDUnionRule [x_var, y_var] x_var,
    -- The constructor is only necessary in diff mode.
    -- It is never applied in trace mode, but will show up in the message theory, which is reassuring for users.
                         mkCUnionRule [x_var, y_var]]
  where x_var = varTerm (LVar "x"  LSortMsg   0)
        y_var = varTerm (LVar "y"  LSortMsg   0)

mkDUnionRule :: [LNTerm] -> LNTerm -> IntrRuleAC
mkDUnionRule t_prems t_conc =
    Rule (DestrRule (append (pack "_") unionSymString) 0 True False [AC Union])
         [kdFact $ fAppAC Union t_prems]
         [kdFact t_conc] [] []

------------------------------------------------------------------------------
-- Xor intruder rules
------------------------------------------------------------------------------

xorIntruderRules ::  [IntrRuleAC]
xorIntruderRules = [mkDXorRule [x_var, y_var] [y_var, z_var] x_xor_z,
                    mkDXorRuleSubterm [x_var, y_var] [y_var] x_var,
                    mkCXorRule x_var y_var x_xor_y,
                    zeroConstructor]
    where x_var   = varTerm (LVar "x"  LSortMsg   0)
          y_var   = varTerm (LVar "y"  LSortMsg   0)
          z_var   = varTerm (LVar "z"  LSortMsg   0)
          x_xor_y = fAppAC Xor [x_var, y_var]
          x_xor_z = fAppAC Xor [x_var, z_var]

mkDXorRule :: [LNTerm] -> [LNTerm] -> LNTerm -> IntrRuleAC
mkDXorRule t_prems t_prems2 t_conc =
    Rule (DestrRule (append (pack "_") xorSymString) 1 False False [AC Xor])
         [kdFact $ fAppAC Xor t_prems, kuFact $ fAppAC Xor t_prems2]
         [kdFact t_conc] [] []

mkDXorRuleSubterm :: [LNTerm] -> [LNTerm] -> LNTerm -> IntrRuleAC
mkDXorRuleSubterm t_prems t_prems2 t_conc =
    Rule (DestrRule (append (pack "_") xorSymString) 1 True False [AC Xor])
         [kdFact $ fAppAC Xor t_prems, kuFact $ fAppAC Xor t_prems2]
         [kdFact t_conc] [] []

mkCXorRule :: LNTerm -> LNTerm -> LNTerm -> IntrRuleAC
mkCXorRule t_prems t_prems2 t_conc =
    Rule (ConstrRule (append (pack "_") xorSymString) (AC Xor))
         [kuFact t_prems, kuFact t_prems2]
         [kuFact t_conc] [kuFact t_conc] []

zeroConstructor :: IntrRuleAC
zeroConstructor = Rule (ConstrRule (append (pack "_") zeroSymString) (NoEq zeroSym))
        [] [kuZero] [kuZero] []
    where
        kuZero = kuFact $ fAppNoEq zeroSym []

mkCUnionRule :: [LNTerm] -> IntrRuleAC
mkCUnionRule terms =
    Rule (ConstrRule (append (pack "_") unionSymString) (AC Union))
         (map kuFact terms)
         [kuFact $ fAppAC Union terms] [kuFact $ fAppAC Union terms] []

------------------------------------------------------------------------------
-- Bilinear Pairing Intruder rules.
------------------------------------------------------------------------------

bpIntruderRules :: Bool -> WithMaude [IntrRuleAC]
bpIntruderRules diff = reader $ \hnd -> minimizeIntruderRules diff hnd $
    [ pmultRule (ConstrRule (append (pack "_") pmultSymString) (NoEq pmultSym)) kuFact return
    , emapRule  (ConstrRule (append (pack "_") emapSymString) (C EMap))  kuFact return
    ]
    ++ -- pmult is similar to exp
    (variantsIntruder hnd id True diff $ pmultRule (DestrRule (append (pack "_") pmultSymString) 0 True False [NoEq pmultSym]) kdFact (const []))
    ++ -- emap is different 
    (bpVariantsIntruder diff hnd $ emapRule (DestrRule (append (pack "_") emapSymString) 0 True False [C EMap]) kdFact (const []))

  where

    x_var_0 = varTerm (LVar "x" LSortMsg 0)
    x_var_1 = varTerm (LVar "x" LSortMsg 1)

    pmultRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact) []
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppPMult (x_var_1, x_var_0)
        concfact = kudFact conc

    emapRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact) []
      where
        bfact = kudFact x_var_0
        efact = kudFact  x_var_1
        conc  = fAppEMap (x_var_0, x_var_1)
        concfact = kudFact conc

bpVariantsIntruder :: Bool -> MaudeHandle -> IntrRuleAC -> [IntrRuleAC]
bpVariantsIntruder diff hnd ru = do
    ruvariant <- variantsIntruder hnd minimizeVariants True diff ru

    -- For the rules "x, pmult(y,z) -> em(x,z)^y" and
    -- "pmult(y,z),x -> em(z,x)^y", we
    -- have to make x a KU premise. Here we rely on the
    -- fact that all other variants are of the form
    -- "pmult(..), pmult(..) -> em(..)"
    case ruvariant of
      Rule i [Fact KDFact an args@[viewTerm -> Lit (Var _)], yfact] concs actions nvs ->
        return $ Rule i [Fact KUFact an args, yfact] concs actions nvs
      Rule i [yfact, Fact KDFact an args@[viewTerm -> Lit (Var _)]] concs actions nvs ->
        return $ Rule i [yfact, Fact KUFact an args] concs actions nvs
      _ -> return ruvariant

  where
    minimizeVariants = nub . map canonize
    canonize subst = canonizeSubst . substFromListVFresh $ zip doms (sort rngs)
      where
        mappings = substToListVFresh subst
        doms     = map fst mappings
        rngs     = map snd mappings

------------------------------------------------------------------------------
-- Classification functions
------------------------------------------------------------------------------

isDRule :: ByteString -> Rule (RuleInfo t IntrRuleACInfo) -> Bool
isDRule ruString ru = case get rInfo ru of
    IntrInfo (DestrRule n _ _ _ _) | n == append (pack "_") ruString -> True
    _                                                                -> False

isDExpRule, isDPMultRule, isDEMapRule
    :: Rule (RuleInfo t IntrRuleACInfo) -> Bool
isDExpRule   = isDRule expSymString
isDPMultRule = isDRule pmultSymString
isDEMapRule  = isDRule emapSymString

isNDCRule :: HasRuleName r => r -> Maybe NDCstate
isNDCRule ru = case ruleName ru of
    IntrInfo (DestrRule _ _ _ _ (f:_)) | isNDCFunSym f -> Just IsNDC
    _                                                  -> Nothing

isNDCDiffRule :: HasRuleName r => r -> Maybe NDCstate
isNDCDiffRule ru = case ruleName ru of
    IntrInfo (DestrRule _ _ _ _ (f:_)) | isNDCDiffFunSym f -> Just IsNDCDiff
    _                                                  -> Nothing
