{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Theory.Tools.IntruderRules (
    subtermIntruderRules
  , dhIntruderRules
  , bpIntruderRules
  , multisetIntruderRules
  , mkDUnionRule
  , specialIntruderRules

  -- ** Classifiers
  , isDExpRule
  , isDEMapRule
  , isDPMultRule
  ) where

import           Control.Basics
import           Control.Monad.Reader

import           Data.List
import qualified Data.Set                        as S
import           Data.ByteString (ByteString)

import           Extension.Data.Label

import           Utils.Misc

import           Term.Maude.Signature
import           Term.Narrowing.Variants.Compute
import           Term.Rewriting.Norm
import           Term.SubtermRule
import           Term.Positions
import           Term.Subsumption

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

-}
-- | @specialIntruderRules@ returns the special intruder rules that are
--   included independently of the message theory
specialIntruderRules :: [IntrRuleAC]
specialIntruderRules =
    [ kuRule CoerceRule      [kdFact x_var]                 (x_var)
    , kuRule PubConstrRule   []                             (x_pub_var)
    , kuRule FreshConstrRule [Fact FreshFact [x_fresh_var]] (x_fresh_var)
    , Rule ISendRule [kuFact x_var]  [Fact InFact [x_var]] [kLogFact x_var]
    , Rule IRecvRule [Fact OutFact [x_var]] [Fact KDFact [x_var]] []
    ]
  where
    kuRule name prems t = Rule name prems [kuFact t] [kuFact t]

    x_var       = varTerm (LVar "x"  LSortMsg   0)
    x_pub_var   = varTerm (LVar "x"  LSortPub   0)
    x_fresh_var = varTerm (LVar "x"  LSortFresh 0)


------------------------------------------------------------------------------
-- Subterm Intruder theory
------------------------------------------------------------------------------

-- | @destuctionRules st@ returns the destruction rules for the given
-- subterm rule @st@
destructionRules :: StRule -> [IntrRuleAC]
destructionRules (StRule lhs@(viewTerm -> FApp (NoEq (f,_)) _) (RhsPosition pos)) =
    go [] lhs pos
  where
    rhs = lhs `atPos` pos
    go _      _                       []     = []
    -- term already in premises
    go _      (viewTerm -> FApp _ _)  (_:[]) = []
    go uprems (viewTerm -> FApp _ as) (i:p)  =
        irule ++ go uprems' t' p
      where
        uprems' = uprems++[ t | (j, t) <- zip [0..] as, i /= j ]
        t'      = as!!i
        irule = if (t' /= rhs && rhs `notElem` uprems')
                then [ Rule (DestrRule f)
                            ((kdFact  t'):(map kuFact uprems'))
                            [kdFact rhs] [] ]
                else []
    go _      (viewTerm -> Lit _)     (_:_)  =
        error "IntruderRules.destructionRules: impossible, position invalid"

destructionRules _ = []

-- | Simple removal of subsumed rules for auto-generated subterm intruder rules.
minimizeIntruderRules :: [IntrRuleAC] -> [IntrRuleAC]
minimizeIntruderRules rules =
    go [] rules
  where
    go checked [] = reverse checked
    go checked (r@(Rule _ prems concs _):unchecked) = go checked' unchecked
      where
        checked' = if any (\(Rule _ prems' concs' _)
                               -> concs' == concs && prems' `subsetOf` prems)
                          (checked++unchecked)
                   then checked
                   else r:checked

-- | @subtermIntruderRules maudeSig@ returns the set of intruder rules for
--   the subterm (not Xor, DH, and MSet) part of the given signature.
subtermIntruderRules :: MaudeSig -> [IntrRuleAC]
subtermIntruderRules maudeSig =
     minimizeIntruderRules $ concatMap destructionRules (S.toList $ stRules maudeSig)
     ++ constructionRules (stFunSyms maudeSig)

-- | @constructionRules fSig@ returns the construction rules for the given
-- function signature @fSig@
constructionRules :: NoEqFunSig -> [IntrRuleAC]
constructionRules fSig =
    [ createRule s k | (s,k) <- S.toList fSig ]
  where
    createRule s k = Rule (ConstrRule s) (map kuFact vars) [concfact] [concfact]
      where vars     = take k [ varTerm (LVar "x"  LSortMsg i) | i <- [0..] ]
            m        = fAppNoEq (s,k) vars
            concfact = kuFact m


------------------------------------------------------------------------------
-- Diffie-Hellman Intruder Rules
------------------------------------------------------------------------------

-- | @dhIntruderRules@ computes the intruder rules for DH
dhIntruderRules :: WithMaude [IntrRuleAC]
dhIntruderRules = reader $ \hnd -> minimizeIntruderRules $
    [ expRule ConstrRule kuFact return
    , invRule ConstrRule kuFact return
    ] ++
    concatMap (variantsIntruder hnd id)
      [ expRule DestrRule kdFact (const [])
      , invRule DestrRule kdFact (const [])
      ]
  where
    x_var_0 = varTerm (LVar "x" LSortMsg 0)
    x_var_1 = varTerm (LVar "x" LSortMsg 1)

    expRule mkInfo kudFact mkAction =
        Rule (mkInfo expSymString) [bfact, efact] [concfact] (mkAction concfact)
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppExp (x_var_0, x_var_1)
        concfact = kudFact conc

    invRule mkInfo kudFact mkAction =
        Rule (mkInfo invSymString) [bfact] [concfact] (mkAction concfact)
      where
        bfact    = kudFact x_var_0
        conc     = fAppInv x_var_0
        concfact = kudFact conc


-- | @variantsIntruder mh irule@ computes the deconstruction-variants
-- of a given intruder rule @irule@
variantsIntruder :: MaudeHandle -> ([LNSubstVFresh] -> [LNSubstVFresh]) -> IntrRuleAC -> [IntrRuleAC]
variantsIntruder hnd minimizeVariants ru = do
    let ruleTerms = concatMap factTerms
                              (get rPrems ru++get rConcs ru++get rActs ru)
    fsigma <- minimizeVariants $ computeVariants (fAppList ruleTerms) `runReader` hnd
    let sigma     = freshToFree fsigma `evalFreshAvoiding` ruleTerms
        ruvariant = normRule' (apply sigma ru) `runReader` hnd
    guard (frees (get rConcs ruvariant) /= [] &&
           -- ground terms are already deducible by applying construction rules
           ruvariant /= ru &&
           -- this is a construction rule
           (get rConcs ruvariant) \\ (get rPrems ruvariant) /= []
           -- The conclusion is included in the premises
           )

    case concatMap factTerms $ get rConcs ruvariant of
        [viewTerm -> FApp (AC Mult) _] ->
            fail "Rules with product conclusion are redundant"
        _                              -> return ruvariant

-- | @normRule irule@ computes the normal form of @irule@
normRule' :: IntrRuleAC -> WithMaude IntrRuleAC
normRule' (Rule i ps cs as) = reader $ \hnd ->
    let normFactTerms = map (fmap (\t -> norm' t `runReader` hnd)) in
    Rule i (normFactTerms ps) (normFactTerms cs) (normFactTerms as)

------------------------------------------------------------------------------
-- Multiset intruder rules
------------------------------------------------------------------------------

multisetIntruderRules ::  [IntrRuleAC]
multisetIntruderRules = [mkDUnionRule [x_var, y_var] x_var]
  where x_var = varTerm (LVar "x"  LSortMsg   0)
        y_var = varTerm (LVar "y"  LSortMsg   0)

mkDUnionRule :: [LNTerm] -> LNTerm -> IntrRuleAC
mkDUnionRule t_prems t_conc =
    Rule (DestrRule unionSymString)
         [kdFact $ fAppAC Union t_prems]
         [kdFact t_conc] []

------------------------------------------------------------------------------
-- Bilinear Pairing Intruder rules.
------------------------------------------------------------------------------

bpIntruderRules :: WithMaude [IntrRuleAC]
bpIntruderRules = reader $ \hnd -> minimizeIntruderRules $
    [ pmultRule ConstrRule kuFact return
    , emapRule  ConstrRule kuFact return
    ]
    ++ -- pmult is similar to exp
    (variantsIntruder hnd id $ pmultRule DestrRule kdFact (const []))
    ++ -- emap is different
    (bpVariantsIntruder hnd $ emapRule DestrRule kdFact (const []) )

  where

    x_var_0 = varTerm (LVar "x" LSortMsg 0)
    x_var_1 = varTerm (LVar "x" LSortMsg 1)

    pmultRule mkInfo kudFact mkAction =
        Rule (mkInfo pmultSymString) [bfact, efact] [concfact] (mkAction concfact)
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppPMult (x_var_1, x_var_0)
        concfact = kudFact conc

    emapRule mkInfo kudFact mkAction =
        Rule (mkInfo emapSymString) [bfact, efact] [concfact] (mkAction concfact)
      where
        bfact = kudFact x_var_0
        efact = kudFact  x_var_1
        conc  = fAppEMap (x_var_0, x_var_1)
        concfact = kudFact conc

bpVariantsIntruder :: MaudeHandle -> IntrRuleAC -> [IntrRuleAC]
bpVariantsIntruder hnd ru = do
    ruvariant <- variantsIntruder hnd minimizeVariants ru

    -- For the rules "x, pmult(y,z) -> em(x,z)^y" and
    -- "pmult(y,z),x -> em(z,x)^y", we
    -- have to make x a KU premise. Here we rely on the
    -- fact that all other variants are of the form
    -- "pmult(..), pmult(..) -> em(..)"
    case ruvariant of
      Rule i [Fact KDFact args@[viewTerm -> Lit (Var _)], yfact] concs actions ->
        return $ Rule i [Fact KUFact args, yfact] concs actions
      Rule i [yfact, Fact KDFact args@[viewTerm -> Lit (Var _)]] concs actions ->
        return $ Rule i [yfact, Fact KUFact args] concs actions
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
    IntrInfo (DestrRule n) | n == ruString -> True
    _                                      -> False

isDExpRule, isDPMultRule, isDEMapRule
    :: Rule (RuleInfo t IntrRuleACInfo) -> Bool
isDExpRule   = isDRule expSymString
isDPMultRule = isDRule pmultSymString
isDEMapRule  = isDRule emapSymString
