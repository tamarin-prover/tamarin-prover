{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Theory.IntruderRules (
    subtermIntruderRules
  , dhIntruderRules
  , xorIntruderRules -- there are no multiset intruder rules
  ) where

import Theory.Rule
-- import Term.DHRules

import Utils.Misc

import Control.Monad.Fresh
import Data.List
import Control.Basics


-- Variants of intruder deduction rules
----------------------------------------------------------------------

------------------------------------------------------------------------------
-- Subterm Intruder theory
------------------------------------------------------------------------------

destructionRules :: (LNTerm, LNTerm) -> [IntrRuleAC]
destructionRules (l@(App (FreeSym (f,_)) _),r)
  | null (frees r) = []
  | otherwise      = go [] l pos
  where
    findRHS t p | t == r = [reverse p]
    findRHS (App _ as) p = concat (zipWith (\a i -> findRHS a (i:p)) as [0..])
    findRHS _  _ = []
    pos = case findRHS l [] of
            p:_ -> p
            _   -> error "IntruderRules.destructionRules: RHS does not occur in LHS, invalid rule"

    go _ _ [] = []
    -- term already in premises
    go _ (App _ _) (_:[]) = []
    go uprems (App _ as) (i:p) =
        irule ++ go uprems' t' p
      where
        uprems' = uprems++[ t | (j, t) <- zip [0..] as, i /= j ]
        t'      = as!!i
        irule = if (t' /= r && r `notElem` uprems')
                 then (`evalFresh` avoid ([r,t']++uprems')) $ do
                     dfact <- kdFact Nothing t'
                     ufacts <- mapM (kdFact Nothing) uprems'
                     concfact <- kdFact Nothing r
                     return [ Rule (IntrApp f) (dfact:ufacts) [concfact] [] ]
                 else []
    go _ (Lit _) (_:_) =
        error "IntruderRules.destructionRules: impossible, position invalid"

destructionRules (_,_) =
    error "IntruderRules.destructionRules: invalid rewriting rule"
    

-- | Simple removal of subsumed rules for auto-generated free intruder rules.
minimizeIntruderRules :: [IntrRuleAC] -> [IntrRuleAC]
minimizeIntruderRules rules = go [] rules
  where
    -- FIXME: this is OK because for all premises and conclusions, the exp tag is
    --        a fresh variable.
    dropExpTag (Fact KUFact [_e,m]) = Fact KUFact [m]
    dropExpTag (Fact KDFact [_e,m]) = Fact KDFact [m]
    dropExpTag t                    = t
    go checked [] = checked
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
     minimizeIntruderRules $ concatMap destructionRules (rrules maudeSig)
     ++ constructionRules (funSig maudeSig)

constructionRules :: FunSig -> [IntrRuleAC]
constructionRules fSig =
    [ createRule s k | (s,k) <- fSig ]
  where
    createRule s k = (`evalFresh` nothingUsed) $ do
        vars     <- map varTerm <$> (sequence $ replicate k (freshLVar "x" LSortMsg))
        pfacts   <- mapM (kuFact Nothing) vars
        concfact <- kuFact (Just IsNoExp) (App (FreeSym (s,k)) vars)
        return $ Rule (IntrApp s) pfacts [concfact] []

{-

t1 = mapM_ print $ destructionRules (sdec(senc(senc(pair(x1,x2),x3),x4),senc(x2,x5)), x2)
t2 = mapM_ print $ destructionRules (sdec(senc(x1,x2),x1), x1)
t3 = mapM_ print $ freeIntruderRules dyRules ++ (dhIntruderRules `runReader` undefined)

-}

------------------------------------------------------------------------------
-- Diffie-Hellman Intruder Rules
------------------------------------------------------------------------------

dhIntruderRules :: WithMaude [IntrRuleAC]
dhIntruderRules = return $
    [expCons]
  where
    expCons = (`evalFresh` nothingUsed) $ do
        b        <- varTerm <$> freshLVar "x" LSortMsg
        e        <- varTerm <$> freshLVar "x" LSortMsg
        bfact    <- kuFact (Just IsNoExp) b
        efact    <- kuFact Nothing e
        concfact <- kuFact (Just IsExp) (App (FreeSym ("exp",2)) [b, e])
        return $ Rule (IntrApp "exp") [efact, bfact] [concfact] []

------------------------------------------------------------------------------
-- Xor Intruder Rules
------------------------------------------------------------------------------

xorIntruderRules :: WithMaude [IntrRuleAC]
xorIntruderRules = return []
  -- TODO: extend XOR tagging