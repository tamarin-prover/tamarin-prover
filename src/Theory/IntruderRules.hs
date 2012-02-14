{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Theory.IntruderRules (
    subtermIntruderRules
  , dhIntruderRules
  , specialIntruderRules
--  , xorIntruderRules -- there are no multiset intruder rules
  ) where

import Theory.Rule
import Term.SubtermRule
import Term.Positions
import Term.Rewriting.Norm
import Term.Narrowing.Variants.Compute

import Utils.Misc

import Control.Monad.Fresh
import Data.List
import Control.Basics
import Extension.Data.Label

import Control.Monad.Reader



-- Variants of intruder deduction rules
----------------------------------------------------------------------


------------------------------------------------------------------------------
-- Special Intruder rules
------------------------------------------------------------------------------

{-
These are the special intruder that are always included.

rule (modulo AC) coerce:
   [ KD( f_, x ) ] --> [ KU( f_, x ) ]

rule (modulo AC) pub:
   [ ] --> [ KU( f_, $x ) ]

rule (modulo AC) gen_fresh:
   [ Fr( ~x ) ] --> [ KU( 'noexp', ~x ) ]

rule (modulo AC) isend:
   [ KU( f_, x) ] --[ K(x) ]-> [ In(x) ]

-}
specialIntruderRules :: [IntrRuleAC]
specialIntruderRules =
    [ Rule CoerceRule
          [Fact KDFact [f_var, x_var]]
          [Fact KUFact [f_var,x_var]]
          []
    , Rule (IntrApp "pub")
          []
          [Fact KUFact [f_var,x_pub_var]]
          [] 
    , Rule (IntrApp "fresh")
          [Fact FreshFact [x_fresh_var]]
          [Fact KUFact [f_var,x_fresh_var]]
          []
    , Rule (IntrApp "isend")
          [Fact KUFact [f_var, x_var]]
          [Fact InFact [x_var]]
          [protoFact Linear "K" [x_var]]
    ]
  where
    f_var       = varTerm (LVar "f_" LSortMsg   0)
    x_var       = varTerm (LVar "x"  LSortMsg   0)
    x_pub_var   = varTerm (LVar "x"  LSortPub   0)
    x_fresh_var = varTerm (LVar "x"  LSortFresh 0)

------------------------------------------------------------------------------
-- Subterm Intruder theory
------------------------------------------------------------------------------

destructionRules :: StRule -> [IntrRuleAC]
destructionRules (StRule lhs@(FApp (NonAC (f,_)) _) (RhsPosition pos)) =
    go [] lhs pos
  where
    rhs = lhs >* pos
    go _ _ [] = []
    -- term already in premises
    go _ (FApp _ _) (_:[]) = []
    go uprems (FApp _ as) (i:p) =
        irule ++ go uprems' t' p
      where
        uprems' = uprems++[ t | (j, t) <- zip [0..] as, i /= j ]
        t'      = as!!i
        irule = if (t' /= rhs && rhs `notElem` uprems')
                 then (`evalFresh` avoid ([rhs,t']++uprems')) $ do
                     dfact <- kdFact Nothing t'
                     ufacts <- mapM (kuFact Nothing) uprems'
                     concfact <- kdFact Nothing rhs
                     return [ Rule (IntrApp f) (dfact:ufacts) [concfact] [] ]
                 else []
    go _ (Lit _) (_:_) =
        error "IntruderRules.destructionRules: impossible, position invalid"

destructionRules _ = []

-- | Simple removal of subsumed rules for auto-generated free intruder rules.
minimizeIntruderRules :: [IntrRuleAC] -> [IntrRuleAC]
minimizeIntruderRules rules =
    go [] rules
  where
    go checked [] = reverse checked
    go checked (r@(Rule _ prems concs _):unchecked) = go checked' unchecked
      where 
        checked' = if any (\(Rule _ prems' concs' _)
                               -> map dropExpTag concs' == map dropExpTag concs &&
                                  map dropExpTag prems' `subsetOf` map dropExpTag prems)
                          (checked++unchecked)
                   then checked
                   else (r:checked)

-- | @freeIntruderRules rus@ returns the set of intruder rules for
--   the free (not Xor, DH, and MSet) part of the given signature.
subtermIntruderRules :: MaudeSig -> [IntrRuleAC]
subtermIntruderRules maudeSig =
     minimizeIntruderRules $ concatMap destructionRules (stRules maudeSig)
     ++ constructionRules (funSig maudeSig)

constructionRules :: FunSig -> [IntrRuleAC]
constructionRules fSig =
    [ createRule s k | (s,k) <- fSig ]
  where
    createRule s k = (`evalFresh` nothingUsed) $ do
        vars     <- map varTerm <$> (sequence $ replicate k (freshLVar "x" LSortMsg))
        pfacts   <- mapM (kuFact Nothing) vars
        concfact <- kuFact (Just CanExp) (FApp (NonAC (s,k)) vars)
        return $ Rule (IntrApp s) pfacts [concfact] []

dropExpTag :: Fact a -> Fact a
dropExpTag (Fact KUFact [_e,m]) = Fact KUFact [m]
dropExpTag (Fact KDFact [_e,m]) = Fact KDFact [m]
dropExpTag t                    = t

------------------------------------------------------------------------------
-- Diffie-Hellman Intruder Rules
------------------------------------------------------------------------------

dhIntruderRules :: WithMaude [IntrRuleAC]
dhIntruderRules = reader $ \hnd -> minimizeIntruderRules $
    [expRule kuFact, invRule kuFact]
    ++ concatMap (variantsIntruder hnd) [expRule kdFact, invRule kdFact]
  where
    expRule kudFact = (`evalFresh` nothingUsed) $ do
        b        <- varTerm <$> freshLVar "x" LSortMsg
        e        <- varTerm <$> freshLVar "x" LSortMsg
        bfact    <- kudFact (Just CanExp) b
        efact    <- kuFact Nothing e
        concfact <- kudFact (Just CannotExp) (FApp (NonAC expSym) [b, e])
        return $ Rule (IntrApp "exp") [bfact, efact] [concfact] []

    invRule kudFact = (`evalFresh` nothingUsed) $ do
        x        <- varTerm <$> freshLVar "x" LSortMsg
        bfact    <- kudFact Nothing x
        concfact <- kudFact (Just CanExp) (FApp (NonAC invSym) [x])
        return $ Rule (IntrApp "inv") [bfact] [concfact] []


variantsIntruder :: MaudeHandle -> IntrRuleAC -> [IntrRuleAC]
variantsIntruder hnd ru = do
    let concTerms = concatMap factTerms
                              (get rPrems ru++get rConcs ru++get rActs ru)
    fsigma <- computeVariants (listToTerm concTerms) `runReader` hnd
    let sigma     = freshToFree fsigma `evalFreshAvoiding` concTerms
        ruvariant = normRule' (apply sigma ru) `runReader` hnd
    guard (frees (get rConcs ruvariant) /= [] &&
           -- ground terms are already deducible by applying construction rules
           ruvariant /= ru &&
           -- this is a construction rule
           (map dropExpTag (get rConcs ruvariant))
           \\ (map dropExpTag (get rPrems ruvariant)) /= []
           -- The conclusion is included in the premises
           )

    case concatMap factTerms $ get rConcs ruvariant of
        [_, FApp (AC Mult) _] ->
            fail "Rules with product conclusion are redundant"
        _                     -> return ruvariant


normRule' :: IntrRuleAC -> WithMaude IntrRuleAC
normRule' (Rule i ps cs as) = reader $ \hnd ->
    let normFactTerms = map (fmap (\t -> norm' t `runReader` hnd)) in
    Rule i (normFactTerms ps) (normFactTerms cs) (normFactTerms as)



{-
------------------------------------------------------------------------------
-- Xor Intruder Rules
------------------------------------------------------------------------------

xorIntruderRules :: WithMaude [IntrRuleAC]
xorIntruderRules = return []
  -- TODO: extend XOR tagging

maude :: IO MaudeHandle
maude = startMaude "maude" allMaudeSig

t :: IO ()
t = do
  m <- maude
  let rules = dhIntruderRules `runReader` m
  mapM_ (putStrLn . render . prettyIntrRuleAC) rules
  writeFile "/tmp/dhrules" $ unlines (map ((++"\n"). render . prettyIntrRuleAC) rules)
  putStrLn ("\nThere are " ++ show (length rules)
            ++ " and " ++ show (length rules - 3) ++ " of these are exp-down rules")
-}
