{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
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
  , stACFunSyms
  , stRules
  , macroNames
  , eqConvergent
  , funSyms
  , irreducibleFunSyms
  , reducibleFunSyms
  , rrulesForMaudeSig
  , noEqFunSyms
  , acUserFunSyms
  , userDefinedFunSyms
  , userDefinedSTFunSyms

  -- * predefined maude signatures
  , dhMaudeSig
  , pairMaudeSig
  , asymEncMaudeSig
  , symEncMaudeSig
  , signatureMaudeSig
  , pairDestMaudeSig
  , asymEncDestMaudeSig
  , symEncDestMaudeSig
  , signatureDestMaudeSig
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
  , addMacroSym
  , addCtxtStRule
  , joinNDCinSig

  -- * pretty printing
  , prettyMaudeSig
  , prettyMaudeSigExcept
  ) where

import           Term.Builtin.Rules
import           Term.LTerm
import           Term.SubtermRule

import Control.Monad.Fresh
-- import Control.Applicative
import Control.DeepSeq

import GHC.Generics (Generic)
import Data.Binary
import Data.Foldable (asum)
import Data.List (intercalate)
-- import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as S

import qualified Data.ByteString.Char8 as BC

import qualified Text.PrettyPrint.Highlight as P

------------------------------------------------------------------------------
-- Maude Signatures
----------------------------------------------------------------------

data MaudeSig = MaudeSig
    { enableDH           :: Bool
    , enableBP           :: Bool
    , enableMSet         :: Bool
    , enableNat          :: Bool
    , enableXor          :: Bool
    , enableDiff         :: Bool
    , stFunSyms          :: S.Set NoEqSym     -- ^ function signature for subterm theory
    , stACFunSyms        :: S.Set ACfctSym    -- ^ user-defined AC function signature
    , stRules            :: S.Set CtxtStRule  -- ^ rewriting rules for subterm theory
    , eqConvergent       :: Bool              -- ^ convergence information for equations
    , macroNames         :: S.Set NoEqSym     -- ^ macro function symbols associated with this signature
    , funSyms            :: FunSig            -- ^ function signature including the
                                              -- function symbols for DH, BP, and Multiset
                                              -- can be computed from enableX and stFunSyms
    , irreducibleFunSyms :: FunSig            -- ^ irreducible function symbols (can be computed)
    , reducibleFunSyms   :: FunSig            -- ^ function symbols @f@ that have a rewriting rule @l→r∈R@ with @root(l)=f@
    }
    deriving (Ord, Show, Eq, Generic, NFData, Binary)

maudeSig :: MaudeSig -> MaudeSig
maudeSig msig@MaudeSig{enableDH, enableBP, enableMSet, enableNat, enableXor, enableDiff = _, stFunSyms, stACFunSyms, stRules, macroNames, eqConvergent} =
  msig {enableDH=enableDH||enableBP, funSyms=allfuns, irreducibleFunSyms=irreduciblefuns, reducibleFunSyms=reducible, eqConvergent=eqConvergent}
  where
    allfuns = S.map NoEq stFunSyms
                `S.union` (if enableDH || enableBP then dhFunSig   else S.empty)
                `S.union` (if enableBP             then bpFunSig   else S.empty)
                `S.union` (if enableMSet           then msetFunSig else S.empty)
                `S.union` (if enableNat            then natFunSig  else S.empty)
                `S.union` (if enableXor            then xorFunSig  else S.empty)
                `S.union` S.map (AC . ACfct) stACFunSyms
    irreduciblefuns = allfuns `S.difference` reducibleWithoutMult
    reducibleWithoutMult =
        S.fromList [ o | CtxtStRule (viewTerm -> FApp o _) _ <- S.toList stRules]
          `S.union` dhReducibleFunSig `S.union` bpReducibleFunSig `S.union` xorReducibleFunSig  --careful! the AC Mult is missing here (probably intentionally)
    reducible = S.fromList [ o | RRule (viewTerm -> FApp o _) _ <- S.toList $ rrulesForMaudeSig msig ]

-- | A monoid instance to combine maude signatures.
instance Semigroup MaudeSig where
    MaudeSig dh1 bp1 mset1 nat1 xor1 diff1 stFunSyms1 stACFunSyms1 stRules1 _ macroNames1 _ _ _ <>
      MaudeSig dh2 bp2 mset2 nat2 xor2 diff2 stFunSyms2 stACFunSyms2 stRules2 _ macroNames2 _ _ _ =
          maudeSig (mempty {enableDH=dh1||dh2
                           ,enableBP=bp1||bp2
                           ,enableMSet=mset1||mset2
                           ,enableNat=nat1||nat2
                           ,enableXor=xor1||xor2
                           ,enableDiff=diff1||diff2
                           ,stFunSyms=unionExceptPairSym stFunSyms1 stFunSyms2
                           ,stACFunSyms=S.union stACFunSyms1 stACFunSyms2
                           ,stRules=unionExceptPairRules stRules1 stRules2
                           ,macroNames=macroNames1 `S.union` macroNames2})
          -- an exception to merging is the destructor variants for pair, which is exclusive
          -- in general, it might make sense to not merge fun syms with same identifier
      where unionExceptPairSym st1 st2 = removeIfNecessary (removeIfNecessary st1 st2 fstSym fstDestSym) st2 sndSym sndDestSym
            unionExceptPairRules st1 st2 = removeIfNecessary (removeIfNecessary st1 st2 fstDestRule fstRule) st2 sndRule sndDestRule
            -- removes y from st1 if x is in st2, and then adds st2 to st1, and vice versa
            removeIfNecessary st1 st2 x y = removeIfNecessary' (removeIfNecessary' st1 st2 x y) st2 y x
            removeIfNecessary' st1 st2 toAdd toRemove = if toAdd `S.member` st2 then
                                         S.union (S.delete toRemove st1) st2
                                       else
                                         S.union st1 st2

instance Monoid MaudeSig where
  mempty = MaudeSig False False False False False False S.empty S.empty S.empty False S.empty S.empty S.empty S.empty

-- | Non-AC function symbols.
noEqFunSyms :: MaudeSig -> NoEqFunSig
noEqFunSyms msig = S.fromList [ o | NoEq o <- S.toList (funSyms msig) ]

-- | AC function symbols.
acUserFunSyms :: MaudeSig -> ACfctFunSig
acUserFunSyms msig = S.fromList [ o | AC (ACfct o) <- S.toList (funSyms msig) ]

userDefinedFunSyms :: MaudeSig -> UserDefinedSig
userDefinedFunSyms msig = S.map NoEqUser (noEqFunSyms msig) `S.union` S.map ACfctUser (acUserFunSyms msig)

userDefinedSTFunSyms :: MaudeSig -> UserDefinedSig
userDefinedSTFunSyms msig = S.map NoEqUser (stFunSyms msig) `S.union` S.map ACfctUser (acUserFunSyms msig)

-- | Add function symbol to given maude signature.
addFunSym :: UserDefinedSym -> MaudeSig -> MaudeSig
addFunSym funsym msig = case funsym of
  NoEqUser f  -> msig `mappend` mempty {stFunSyms=S.fromList [f]}
  ACfctUser f -> msig `mappend` mempty {stACFunSyms=S.fromList [f]}

-- | Add a macro symbol to given maude signature.
addMacroSym :: NoEqSym -> MaudeSig -> MaudeSig
addMacroSym funsym msig =
  msig `mappend` mempty {macroNames=S.fromList [funsym]}

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
pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, revealSignatureMaudeSig, hashMaudeSig, locationReportMaudeSig, symEncDestMaudeSig, asymEncDestMaudeSig, signatureDestMaudeSig, pairDestMaudeSig :: MaudeSig
pairMaudeSig            = maudeSig $ mempty {stFunSyms=pairFunSig,stRules=pairRules}
symEncMaudeSig          = maudeSig $ mempty {stFunSyms=symEncFunSig,stRules=symEncRules}
asymEncMaudeSig         = maudeSig $ mempty {stFunSyms=asymEncFunSig,stRules=asymEncRules}
signatureMaudeSig       = maudeSig $ mempty {stFunSyms=signatureFunSig,stRules=signatureRules}
revealSignatureMaudeSig = maudeSig $ mempty {stFunSyms=revealSignatureFunSig,stRules=revealSignatureRules}
hashMaudeSig            = maudeSig $ mempty {stFunSyms=hashFunSig}
locationReportMaudeSig            = maudeSig $ mempty {stFunSyms=locationReportFunSig, stRules=locationReportRules}
symEncDestMaudeSig          = maudeSig $ mempty {stFunSyms=symEncFunDestSig,stRules=symEncDestRules}
asymEncDestMaudeSig         = maudeSig $ mempty {stFunSyms=asymEncFunDestSig,stRules=asymEncDestRules}
signatureDestMaudeSig       = maudeSig $ mempty {stFunSyms=signatureFunDestSig,stRules=signatureDestRules}
pairDestMaudeSig            = maudeSig $ mempty {stFunSyms=pairFunDestSig,stRules=pairDestRules}

-- | The minimal maude signature.
minimalMaudeSig :: Bool -> MaudeSig
minimalMaudeSig flag = maudeSig $ mempty {enableDiff=flag,stFunSyms=pairFunSig,stRules=pairRules}
-- essentially pairMaudeSig, but with the enableDiff flag set according to "flag"
-- -- MaudeSig False False False flag pairFunSig pairRules S.empty S.empty

-- | Signature with enableDiff set to True
enableDiffMaudeSig :: MaudeSig
enableDiffMaudeSig = maudeSig $ mempty {enableDiff=True}

-- | Adds the given NDC state to a specific function symbol in the signature. The symbol is
--   identified by name, as the NDC state of the given symbol may differ from the one in the
--   signature (e.g., for symbols taken from the metadata of diff-mode intruder rules).
joinNDCinSig :: MaudeSig -> FunSym -> NDCstate -> MaudeSig
joinNDCinSig sig funSym ndcState = sig {stFunSyms = S.map updNoEq (stFunSyms sig)}
                                       {stACFunSyms = S.map updAC (stACFunSyms sig)}
  where
    fName (NoEq (n,_))       = Just n
    fName (AC (ACfct (n,_))) = Just n
    fName _                  = Nothing
    updNoEq x@(n,_) = if Just n == fName funSym then setNDCNoEqSym (joinNDC ndcState (ndcNoEq x)) x else x
    updAC x@(n,_)   = if Just n == fName funSym then setNDCACfctSym (joinNDC ndcState (ndcAC x)) x else x
    ndcNoEq (_,(_,_,_,ndc)) = ndc
    ndcAC (_,(_,_,ndc))     = ndc

------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

prettyMaudeSigExcept :: P.HighlightDocument d => MaudeSig -> S.Set UserDefinedSym -> d
prettyMaudeSigExcept sig excl = P.vcat
    [ ppNonEmptyList' "builtins:"  P.text      builtIns
    , ppNonEmptyList' "functions:" ppFunSymb (S.toList (S.map NoEqUser (stFunSyms sig S.\\ exclNoEq)) ++ S.toList (S.map ACfctUser (stACFunSyms sig S.\\ exclAC)))
    , ppNonEmptyList
        (\ds -> P.sep ((if eqConvergent sig then P.keyword_ "equations [convergent]:" else P.keyword_ "equations:") : map (P.nest 2) ds))
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

    ppFunSymb (NoEqUser (f,(k,priv,constr,ndc))) = P.text $ BC.unpack f ++ "/" ++ show k
                                             ++ showAttrs (attrsNoEq priv constr ++ attrsNDC ndc)
      where
            attrsNoEq Public Destructor = ["destructor"]
            attrsNoEq Private Destructor = ["private","destructor"]
            attrsNoEq Private Constructor = ["private","constructor"]
            attrsNoEq Public Constructor = []

    ppFunSymb (ACfctUser (f,(priv,constr,ndc))) = P.text $ BC.unpack f ++ "/2"
                                             ++ showAttrs (attrsAC priv constr ++ ["AC"] ++ attrsNDC ndc)
      where
            attrsAC Public Destructor = ["destructor"]
            attrsAC Private Destructor = ["private","destructor"]
            attrsAC Private Constructor = ["private"]
            attrsAC Public Constructor = []

    attrsNDC ndc = ["NDC" | hasNDC ndc] ++ ["NDC-diff" | hasNDCdiff ndc]

    showAttrs [] = ""
    showAttrs as = " [" ++ intercalate "," as ++ "]"

    exclNoEq = S.fromList [ o | NoEqUser o <- S.toList excl ]
    exclAC = S.fromList [ o | ACfctUser o <- S.toList excl ]

prettyMaudeSig :: P.HighlightDocument d => MaudeSig -> d
prettyMaudeSig sig  = prettyMaudeSigExcept sig S.empty
