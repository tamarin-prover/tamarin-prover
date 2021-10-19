{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Equational signatures for Maude.
module Term.Maude.Signature (
  -- * Maude signatures
    MaudeSig
  , enableDH
  , enableBP
  , enableMSet
  , enableDiff
  , enableXor
  , enableNat
  , stFunSyms
  , stRules
  , funSyms
  , userACSyms
  , userACSyms'
  , irreducibleFunSyms
  , reducibleFunSyms
  , rrulesForMaudeSig
  , noEqFunSyms
  , userSortsForMaudeSig

  -- * predefined maude signatures
  , dhMaudeSig
  , pairMaudeSig
  , asymEncMaudeSig
  , symEncMaudeSig
  , signatureMaudeSig
  , revealSignatureMaudeSig
  , locationReportMaudeSig
  , hashMaudeSig
  , msetMaudeSig
  , natMaudeSig
  , bpMaudeSig
  , xorMaudeSig
  , minimalMaudeSig
  , enableDiffMaudeSig

  -- * extend maude signatures
  , addFunSym
  , addCtxtStRule
  , addUserSort
  , addUserACSym

  -- * pretty printing
  , prettyMaudeSig
  ) where

import Term.Term
import Term.LTerm
import Term.Builtin.Rules
import Term.SubtermRule

import Control.Monad.Fresh
-- import Control.Applicative
import Control.DeepSeq

import Data.Maybe  --TODO-UNCERTAIN: needed?
import GHC.Generics (Generic)
import Data.Binary
import Data.Foldable (asum)
-- import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as S

import qualified Data.ByteString.Char8 as BC

import qualified Text.PrettyPrint.Highlight as P
import Debug.Trace

------------------------------------------------------------------------------
-- Maude Signatures
----------------------------------------------------------------------

-- | The required information to define a @Maude functional module@.
data MaudeSig = MaudeSig  --TODO-MY add new field with custom sorts
    { enableDH           :: Bool
    , enableBP           :: Bool
    , enableMSet         :: Bool
    , enableNat          :: Bool
    , enableXor          :: Bool
    , enableDiff         :: Bool
    , stFunSyms          :: S.Set NoEqSym -- ^ function signature for subterm theory TODO-MY: change to Set FunSym
    , stRules            :: S.Set CtxtStRule  -- ^ rewriting rules for subterm theory

    , funSyms            :: FunSig        -- ^ function signature including the
                                          -- function symbols for DH, BP, and Multiset
                                          -- can be computed from enableX and stFunSyms
    , irreducibleFunSyms :: FunSig        -- ^ irreducible function symbols (can be computed)
    , reducibleFunSyms   :: FunSig        -- ^ function symbols @f@ that have a rewriting rule @l→r∈R@ with @root(l)=f@
    , userSorts          :: S.Set String  -- ^ user-defined sorts
    , userACSyms         :: S.Set ACSym   -- ^ user-defined AC symbols
    }
    deriving (Ord, Show, Eq, Generic, NFData, Binary)

-- | Smart constructor for maude signatures. Computes funSyms and irreducibleFunSyms.
maudeSig :: MaudeSig -> MaudeSig
maudeSig msig@MaudeSig {enableDH, enableBP, enableMSet, enableNat, enableXor, enableDiff = _, stFunSyms, stRules} =
    msig {enableDH=enableDH||enableBP, funSyms=allfuns, irreducibleFunSyms=irreduciblefuns, reducibleFunSyms=reducible}
  where
    -- TODO-UNCERTAIN: (todo from Cedric) Take into accounts user-defined AC function symbols.
    allfuns = S.map NoEq stFunSyms
                `S.union` (if enableDH || enableBP then dhFunSig   else S.empty)
                `S.union` (if enableBP             then bpFunSig   else S.empty)
                `S.union` (if enableMSet           then msetFunSig else S.empty)
                `S.union` (if enableNat            then natFunSig  else S.empty)
                `S.union` (if enableXor            then xorFunSig  else S.empty)
    irreduciblefuns = allfuns `S.difference` reducibleWithoutMult
    reducibleWithoutMult =
        S.fromList [ o | CtxtStRule (viewTerm -> FApp o _) _ <- S.toList stRules]
          `S.union` dhReducibleFunSig `S.union` bpReducibleFunSig `S.union` xorReducibleFunSig  --careful! the AC Mult is missing here (probably intentionally)
    reducible = S.fromList [ o | RRule (viewTerm -> FApp o _) _ <- S.toList $ rrulesForMaudeSig msig ]

-- | A monoid instance to combine maude signatures.
instance Semigroup MaudeSig where
    MaudeSig dh1 bp1 mset1 nat1 xor1 diff1 stFunSyms1 stRules1 _ _ _ uSorts1 uSyms1 <>
      MaudeSig dh2 bp2 mset2 nat2 xor2 diff2 stFunSyms2 stRules2 _ _ _ uSorts2 uSyms2 =
          maudeSig (mempty {enableDH=dh1||dh2
                           ,enableBP=bp1||bp2
                           ,enableMSet=mset1||mset2
                           ,enableNat=nat1||nat2
                           ,enableXor=xor1||xor2
                           ,enableDiff=diff1||diff2
                           ,stFunSyms=S.union stFunSyms1 stFunSyms2
                           ,stRules=S.union stRules1 stRules2
                           ,userSorts=S.union uSorts1 uSorts2
                           ,userACSyms=S.union uSyms1 uSyms2})

instance Monoid MaudeSig where
    mempty = MaudeSig False False False False False False S.empty S.empty S.empty S.empty S.empty S.empty S.empty

-- | Non-AC function symbols.
noEqFunSyms :: MaudeSig -> NoEqFunSig
noEqFunSyms msig = S.fromList [ o | NoEq o <- S.toList (funSyms msig) ]

-- | Add function symbol to given maude signature.
addFunSym :: NoEqSym -> MaudeSig -> MaudeSig
addFunSym funsym msig =
    msig `mappend` mempty {stFunSyms=S.fromList [funsym]}

-- | Add a user-defined sort to given maude signature.
addUserSort :: String -> MaudeSig -> MaudeSig
addUserSort str msig =
    msig `mappend` mempty {userSorts=S.fromList [str]}

-- | Add a user-defined AC symbol to given maude signature.
addUserACSym :: ACSym -> MaudeSig -> MaudeSig
addUserACSym sym msig =
    msig `mappend` mempty {userACSyms=S.fromList [sym]}


-- | Add subterm rule to given maude signature.
addCtxtStRule :: CtxtStRule -> MaudeSig -> MaudeSig
addCtxtStRule str msig =
    msig `mappend` mempty {stRules=S.fromList [str]}

-- | Returns all rewriting rules including the rules
--   for DH, BP, and multiset.
rrulesForMaudeSig :: MaudeSig -> Set (RRule LNTerm)
rrulesForMaudeSig (MaudeSig {enableDH, enableBP, enableMSet, enableXor, stRules}) =
    (S.map ctxtStRuleToRRule stRules)
    `S.union` (if enableDH   then dhRules   else S.empty)
    `S.union` (if enableBP   then bpRules   else S.empty)
    `S.union` (if enableMSet then msetRules else S.empty)
    `S.union` (if enableXor  then xorRules  else S.empty)
    
-- | Extract sorts from maude signature substitution rules.
sortsForMaudeSig :: MaudeSig -> Set LSort
sortsForMaudeSig msig =
    S.fromList $ map getLSort $ S.toList $ stRules msig
  where
    getLSort (CtxtStRule lnterm _) = sortOfLNTerm lnterm

-- | Extract user-defined sorts from maude signature.
userSortsForMaudeSig :: MaudeSig -> Set LSort
userSortsForMaudeSig msig =
    S.union
      (S.map LSortUser $ userSorts msig)
      (S.filter isUserDefined $ sortsForMaudeSig msig)
  where
    isUserDefined (LSortUser _) = True
    isUserDefined _             = False

userACSyms' :: MaudeSig -> [String]
userACSyms' msig = catMaybes $ map sym $ S.toList $ userACSyms msig
  where 
    sym (UserAC f _) = Just f
    sym _            = Nothing


------------------------------------------------------------------------------
-- Builtin maude signatures
------------------------------------------------------------------------------

-- | Maude signatures for the AC symbols.
dhMaudeSig, bpMaudeSig, msetMaudeSig, natMaudeSig, xorMaudeSig :: MaudeSig
dhMaudeSig   = maudeSig $ mempty {enableDH=True}
bpMaudeSig   = maudeSig $ mempty {enableBP=True}
msetMaudeSig = maudeSig $ mempty {enableMSet=True}
natMaudeSig  = maudeSig $ mempty {enableNat=True}
xorMaudeSig  = maudeSig $ mempty {enableXor=True}

-- | Maude signatures for the default subterm symbols.
--pairMaudeSig :: Bool -> MaudeSig
--pairMaudeSig flag = maudeSig $ mempty {stFunSyms=pairFunSig,stRules=pairRules,enableDiff=flag}
pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, revealSignatureMaudeSig, hashMaudeSig, locationReportMaudeSig :: MaudeSig
pairMaudeSig            = maudeSig $ mempty {stFunSyms=pairFunSig,stRules=pairRules}
symEncMaudeSig          = maudeSig $ mempty {stFunSyms=symEncFunSig,stRules=symEncRules}
asymEncMaudeSig         = maudeSig $ mempty {stFunSyms=asymEncFunSig,stRules=asymEncRules}
signatureMaudeSig       = maudeSig $ mempty {stFunSyms=signatureFunSig,stRules=signatureRules}
revealSignatureMaudeSig = maudeSig $ mempty {stFunSyms=revealSignatureFunSig,stRules=revealSignatureRules}
hashMaudeSig            = maudeSig $ mempty {stFunSyms=hashFunSig}
locationReportMaudeSig            = maudeSig $ mempty {stFunSyms=locationReportFunSig, stRules=locationReportRules}

-- | The minimal maude signature.
minimalMaudeSig :: Bool -> MaudeSig
minimalMaudeSig flag = maudeSig $ mempty {enableDiff=flag,stFunSyms=pairFunSig,stRules=pairRules}
-- essentially pairMaudeSig, but with the enableDiff flag set according to "flag"
-- -- MaudeSig False False False flag pairFunSig pairRules S.empty S.empty

-- | Signature with enableDiff set to True
enableDiffMaudeSig :: MaudeSig
enableDiffMaudeSig = maudeSig $ mempty {enableDiff=True}

------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

prettyMaudeSig :: P.HighlightDocument d => MaudeSig -> d
prettyMaudeSig sig = P.vcat
    [ ppNonEmptyList' "builtins:"  P.text     builtIns
    , ppNonEmptyList' "usersorts:" P.text  $  S.toList (userSorts sig)
    , ppNonEmptyList' "functions:" ppFun   $  (map Left  $ S.toList $ stFunSyms sig)
                                           ++ (map Right $ S.toList $ userACSyms sig)
    , ppNonEmptyList
        (\ds -> P.sep (P.keyword_ "equations:" : map (P.nest 2) ds))
        prettyCtxtStRule $ S.toList (stRules sig)
    ]
  where
    ppNonEmptyList' name     = ppNonEmptyList ((P.keyword_ name P.<->) . P.fsep)
    ppNonEmptyList _   _  [] = P.emptyDoc
    ppNonEmptyList hdr pp xs = hdr $ P.punctuate P.comma $ map pp xs

    builtIns = asum $ map (\(f, x) -> guard (f sig) *> pure x)
      [ (enableDH,   "diffie-hellman")
      , (enableBP,   "bilinear-pairing")
      , (enableMSet, "multiset")
      , (enableNat,  "natural-numbers")
      , (enableXor,  "xor")
      ]
            
    ppFun (Left noeq) = ppNoEqFunSymb noeq
    ppFun (Right acs) = ppACSym acs

    ppACSym (UserAC f s) = P.text $ f ++ ": " ++ s ++ " " ++ s ++ " -> " ++ s ++ " [AC]"
    ppACSym _            = P.text ""

    ppNoEqFunSymb (NoEqSym f k priv sorts) = P.text $ 
        case sorts of
          Nothing  -> BC.unpack f ++ "/" ++ show k ++ showPriv priv
          Just sts -> BC.unpack f ++ ":" ++ showSorts sts ++ showPriv priv
      where
        showPriv Private = " [private]"
        showPriv Public  = ""

        showSorts []     = ""
        showSorts [x]    = " -> " ++ x
        showSorts (x:xs) = " " ++ x ++ showSorts xs 
