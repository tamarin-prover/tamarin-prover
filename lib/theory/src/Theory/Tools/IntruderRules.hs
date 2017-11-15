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
  , variantsIntruder

  -- ** Classifiers
  , isDExpRule
  , isDEMapRule
  , isDPMultRule
  ) where

import           Control.Basics hiding (empty)
import           Control.Monad.Reader

import           Data.List
import qualified Data.Set                          as S
import           Data.ByteString.Char8 (ByteString, append, pack, empty)

import           Extension.Data.Label

import           Utils.Misc

import           Term.Maude.Signature
import           Term.Narrowing.Variants.Compute
import           Term.Rewriting.Norm
import           Term.SubtermRule
import           Term.Subsumption
import           Term.Positions

import           Theory.Model

-- import           Debug.Trace

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
    [ kuRule CoerceRule      [kdFact x_var]                 (x_var)
    , kuRule PubConstrRule   []                             (x_pub_var)
    , kuRule FreshConstrRule [Fact FreshFact [x_fresh_var]] (x_fresh_var)
    , Rule ISendRule [kuFact x_var]  [Fact InFact [x_var]] [kLogFact x_var]
    , Rule IRecvRule [Fact OutFact [x_var]] [Fact KDFact [x_var]] []
    ] ++
    if diff 
       then [ Rule IEqualityRule [kuFact x_var, kdFact x_var]  [] [] ]
       else []
  where
    kuRule name prems t = Rule name prems [kuFact t] [kuFact t]

    x_var       = varTerm (LVar "x"  LSortMsg   0)
    x_pub_var   = varTerm (LVar "x"  LSortPub   0)
    x_fresh_var = varTerm (LVar "x"  LSortFresh 0)


------------------------------------------------------------------------------
-- Subterm Intruder theory
------------------------------------------------------------------------------

-- | @destuctionRules diff st@ returns the destruction rules for the given
-- context subterm rule @st@
destructionRules :: Bool -> CtxtStRule -> [IntrRuleAC]
destructionRules bool (CtxtStRule lhs@(viewTerm -> FApp _ _) (StRhs (pos:[]) rhs)) | (bool || (frees rhs /= []) || (containsPrivate rhs)) =
    go [] lhs pos empty []
  where
    go _      _                       []     _ _                     = []
    -- term already in premises, but necessary for constant conclusions
    go _      (viewTerm -> FApp _ _)  (_:[]) _ _ | (frees rhs /= []) = []
    go uprems (viewTerm -> FApp (NoEq (f,(_,Public))) as) (i:p) n pd =
        irule ++ go uprems' t' p funs posname
      where
        uprems' = uprems++[ t | (j, t) <- zip [0..] as, i /= j ]
        t'      = as!!i
        funs = append (append n (pack "_")) f
        posname = "_" ++ show i ++ pd
        name    = append (pack posname) funs
        irule = if {-trace (show lhs ++ " " ++ show pos ++ " " ++ show posname ++ " " ++ show rhs ++ " " ++ show (lhs `atPos` pos) ++ " " ++ show (frees rhs == []))-} (t' /= rhs && rhs `notElem` uprems')
                then [ Rule (DestrRule name (-1) (rhs == lhs `atPos` pos) (frees rhs == []))
                            ((kdFact  t'):(map kuFact uprems'))
                            [kdFact rhs] [] ]
                else []
    go _      (viewTerm -> FApp (NoEq (_,(_,Private))) _) _     _ _  = []
    go _      (viewTerm -> Lit _)                         (_:_) _ _  =
        error "IntruderRules.destructionRules: impossible, position invalid"   
     
destructionRules bool (CtxtStRule lhs (StRhs (pos:posit) rhs)) 
    | (bool || (frees rhs /= []) || (containsPrivate rhs)) = 
       destructionRules bool (CtxtStRule lhs (StRhs [pos] rhs)) 
           ++ destructionRules bool (CtxtStRule lhs (StRhs posit rhs))
destructionRules _ _ = []

-- returns all equations with private constructors on the RHS
privateConstructorEquations :: [CtxtStRule] -> [(LNTerm, ByteString)]
privateConstructorEquations rs = case rs of
    []    -> []
    (CtxtStRule lhs (StRhs _ (viewTerm -> FApp (NoEq (vname,(0,Private))) _))):xs
          -> (lhs, vname):(privateConstructorEquations xs)
    _:xs  -> privateConstructorEquations xs
    
-- given equations with private constructors on the RHS and a list of private function names x,
-- returns the list of all such constructors such that the LHS only contains public functions or functions in x
derivablePrivateConstants :: [(LNTerm, ByteString)] -> [ByteString] -> [ByteString]
derivablePrivateConstants eqs x =
    if any (containsNoPrivateExcept x) (map fst eqs)
        then
            derivablePrivateConstants (filter (\(l, _) -> not $ containsNoPrivateExcept x l) eqs) (x ++ map snd (filter (\(l, _) -> containsNoPrivateExcept x l) eqs)) 
        else
            x

-- | @privateConstructorRules st@ returns the constructor rules for private constants that are consequences of rewrite rules in @st@
privateConstructorRules :: [CtxtStRule] -> [IntrRuleAC]
privateConstructorRules rules = map createRule $ derivablePrivateConstants (privateConstructorEquations rules) []
  where
    -- creates a constructor rule for constant s
    createRule s = Rule (ConstrRule (append (pack "_") s)) [] [concfact] [concfact]
      where m        = fAppNoEq (s,(0,Private)) []
            concfact = kuFact m

-- | Simple removal of subsumed rules for auto-generated subterm intruder rules.
minimizeIntruderRules :: Bool -> [IntrRuleAC] -> [IntrRuleAC]
minimizeIntruderRules diff rules = 
    filter (\x -> not $ isDoublePremiseRule x) 
      $ if diff then rules else go [] rules
  where
    go checked [] = reverse checked
    go checked (r@(Rule _ prems concs _):unchecked) = go checked' unchecked
      where
        checked' = if any (\(Rule _ prems' concs' _)
                               -> concs' == concs && prems' `subsetOf` prems)
                          (checked++unchecked)
                   then checked
                   else r:checked
    
    -- We assume that the KD-Fact is the first fact, which is the case in destructionRules above
    isDoublePremiseRule (Rule _ ((Fact KDFact [t]):prems) concs _) = 
        frees concs == []
         && not (any containsPrivate (t:(concat $ map getFactTerms prems)))
         && isMsgVar t && any (==(Fact KUFact [t])) prems
    isDoublePremiseRule _                                               = False

-- | @subtermIntruderRules diff maudeSig@ returns the set of intruder rules for
--   the subterm (not Xor, DH, and MSet) part of the given signature.
subtermIntruderRules :: Bool -> MaudeSig -> [IntrRuleAC]
subtermIntruderRules diff maudeSig =
   minimizeIntruderRules diff $ concatMap (destructionRules diff) (S.toList $ stRules maudeSig)
     ++ constructionRules (stFunSyms maudeSig) ++ privateConstructorRules (S.toList $ stRules maudeSig) 

-- | @constructionRules fSig@ returns the construction rules for the given
-- function signature @fSig@
constructionRules :: NoEqFunSig -> [IntrRuleAC]
constructionRules fSig =
    [ createRule s k | (s,(k,Public)) <- S.toList fSig ]
  where
    createRule s k = Rule (ConstrRule (append (pack "_") s)) (map kuFact vars) [concfact] [concfact]
      where vars     = take k [ varTerm (LVar "x"  LSortMsg i) | i <- [0..] ]
            m        = fAppNoEq (s,(k,Public)) vars
            concfact = kuFact m

------------------------------------------------------------------------------
-- Diffie-Hellman Intruder Rules
------------------------------------------------------------------------------

-- | @dhIntruderRules@ computes the intruder rules for DH
dhIntruderRules :: Bool -> WithMaude [IntrRuleAC]
dhIntruderRules diff = reader $ \hnd -> minimizeIntruderRules diff $
    [ expRule  (ConstrRule (append (pack "_") expSymString))  kuFact return
    , invRule  (ConstrRule (append (pack "_") invSymString))  kuFact return
    -- The constructors for one and mult are only necessary in diff mode.
    -- They are never applied in trace mode as all corresponding goals are solved directly,
    -- but they  will show up in the message theory, which is reassuring for users.
    , oneRule  (ConstrRule (append (pack "_") oneSymString))  kuFact return
    , multRule (ConstrRule (append (pack "_") multSymString)) kuFact return
    ] ++
    concatMap (variantsIntruder hnd id True)
      [ expRule (DestrRule (append (pack "_") expSymString) 0 True False) kdFact (const [])
      , invRule (DestrRule (append (pack "_") invSymString) 0 True False) kdFact (const [])
      ]
  where
    x_var_0 = varTerm (LVar "x" LSortMsg 0)
    x_var_1 = varTerm (LVar "x" LSortMsg 1)

    expRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact)
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppExp (x_var_0, x_var_1)
        concfact = kudFact conc

    multRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact)
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppAC Mult [x_var_0, x_var_1]
        concfact = kudFact conc

    invRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact] [concfact] (mkAction concfact)
      where
        bfact    = kudFact x_var_0
        conc     = fAppInv x_var_0
        concfact = kudFact conc

    oneRule mkInfo kudFact mkAction =
        Rule mkInfo [] [concfact] (mkAction concfact)
      where
        conc     = fAppNoEq oneSym []
        concfact = kudFact conc


-- | @variantsIntruder mh irule@ computes the deconstruction-variants
-- of a given intruder rule @irule@
variantsIntruder :: MaudeHandle -> ([LNSubstVFresh] -> [LNSubstVFresh]) -> Bool -> IntrRuleAC -> [IntrRuleAC]
variantsIntruder hnd minimizeVariants applyFilters ru = go [] $ reverse $ do
    let ruleTerms = concatMap factTerms
                              (get rPrems ru++get rConcs ru++get rActs ru)
    fsigma <- minimizeVariants $ computeVariants (fAppList ruleTerms) `runReader` hnd
    let sigma     = freshToFree fsigma `evalFreshAvoiding` ruleTerms
        ruvariant = normRule' (apply sigma ru) `runReader` hnd
    guard (not applyFilters || frees (get rConcs ruvariant) /= [] &&
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
normRule' (Rule i ps cs as) = reader $ \hnd ->
    let normFactTerms = map (fmap (\t -> norm' t `runReader` hnd)) in
    Rule i (normFactTerms ps) (normFactTerms cs) (normFactTerms as)

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
    Rule (DestrRule (append (pack "_") unionSymString) 0 True False)
         [kdFact $ fAppAC Union t_prems]
         [kdFact t_conc] []

mkCUnionRule :: [LNTerm] -> IntrRuleAC
mkCUnionRule terms =
    Rule (ConstrRule (append (pack "_") unionSymString))
         (map kuFact terms)
         [kuFact $ fAppAC Union terms] [kuFact $ fAppAC Union terms]

------------------------------------------------------------------------------
-- Bilinear Pairing Intruder rules.
------------------------------------------------------------------------------

bpIntruderRules :: Bool -> WithMaude [IntrRuleAC]
bpIntruderRules diff = reader $ \hnd -> minimizeIntruderRules diff $
    [ pmultRule (ConstrRule (append (pack "_") pmultSymString)) kuFact return
    , emapRule  (ConstrRule (append (pack "_") emapSymString))  kuFact return
    ]
    ++ -- pmult is similar to exp
    (variantsIntruder hnd id True $ pmultRule (DestrRule (append (pack "_") pmultSymString) 0 True False) kdFact (const []))
    ++ -- emap is different
    (bpVariantsIntruder hnd $ emapRule (DestrRule (append (pack "_") emapSymString) 0 True False) kdFact (const []))

  where

    x_var_0 = varTerm (LVar "x" LSortMsg 0)
    x_var_1 = varTerm (LVar "x" LSortMsg 1)

    pmultRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact)
      where
        bfact = kudFact x_var_0
        efact = kuFact  x_var_1
        conc = fAppPMult (x_var_1, x_var_0)
        concfact = kudFact conc

    emapRule mkInfo kudFact mkAction =
        Rule mkInfo [bfact, efact] [concfact] (mkAction concfact)
      where
        bfact = kudFact x_var_0
        efact = kudFact  x_var_1
        conc  = fAppEMap (x_var_0, x_var_1)
        concfact = kudFact conc

bpVariantsIntruder :: MaudeHandle -> IntrRuleAC -> [IntrRuleAC]
bpVariantsIntruder hnd ru = do
    ruvariant <- variantsIntruder hnd minimizeVariants True ru

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
    IntrInfo (DestrRule n _ _ _) | n == (append (pack "_") ruString) -> True
    _                                                                -> False

isDExpRule, isDPMultRule, isDEMapRule
    :: Rule (RuleInfo t IntrRuleACInfo) -> Bool
isDExpRule   = isDRule expSymString
isDPMultRule = isDRule pmultSymString
isDEMapRule  = isDRule emapSymString
