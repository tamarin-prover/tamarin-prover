{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving, TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators,FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Signatures for the terms and multiset rewriting rules used to model and
-- reason about a security protocol.
-- modulo the full Diffie-Hellman equational theory and once modulo AC.
module Theory.Signature (

  -- * Signature type
    Signature
  
  -- ** Pure signatures
  , SignaturePure
  , emptySignaturePure
  , sigpUniqueInsts
  , sigpMaudeSig

  -- ** Using Maude to handle operations relative to a 'Signature'
  , SignatureWithMaude
  , toSignatureWithMaude
  , toSignaturePure
  , sigmUniqueInsts
  , sigmMaudeHandle

  -- ** Pretty-printing
  , prettySignature

  ) where

import qualified Data.Set                            as S
import qualified Data.Label                          as L

import           Control.Applicative
import           Control.DeepSeq

import           Theory.Pretty
import           Theory.Fact
import           Term.SubtermRule

import           Data.DeriveTH
import           Data.Binary

import           System.IO.Unsafe (unsafePerformIO)

-- | A theory signature.
data Signature a = Signature
       { _sigUniqueInsts :: S.Set FactTag
         -- ^ Fact symbols that are assumed to have unique instances.
       , _sigMaudeInfo  :: a
       }

$(L.mkLabels [''Signature])

$(derive makeBinary ''FactTag)
$(derive makeBinary ''MaudeSig)
$(derive makeBinary ''StRhs)
$(derive makeBinary ''Term )
$(derive makeBinary ''Lit)
$(derive makeBinary ''ACSym)
$(derive makeBinary ''FunSym)
$(derive makeBinary ''LSort)
$(derive makeBinary ''LVar)
$(derive makeBinary ''BVar)
$(derive makeBinary ''NameTag)
$(derive makeBinary ''NameId)
$(derive makeBinary ''Name)
$(derive makeBinary ''StRule)
$(derive makeBinary ''Multiplicity)

$(derive makeNFData ''FactTag)
$(derive makeNFData ''Term)
$(derive makeNFData ''NameTag)
$(derive makeNFData ''NameId)
$(derive makeNFData ''Name)
$(derive makeNFData ''Lit)
$(derive makeNFData ''ACSym)
$(derive makeNFData ''FunSym)
$(derive makeNFData ''LSort)
$(derive makeNFData ''LVar)
$(derive makeNFData ''BVar)
$(derive makeNFData ''MaudeSig)
$(derive makeNFData ''StRhs)
$(derive makeNFData ''StRule)
$(derive makeNFData ''Multiplicity)

------------------------------------------------------------------------------
-- Pure Signatures
------------------------------------------------------------------------------

-- | A 'Signature' without an associated Maude process.
type SignaturePure = Signature MaudeSig

-- | Access the globally fresh field.
sigpUniqueInsts :: SignaturePure L.:-> S.Set FactTag
sigpUniqueInsts = sigUniqueInsts

-- | Access the maude signature.
sigpMaudeSig:: SignaturePure L.:-> MaudeSig
sigpMaudeSig = sigMaudeInfo

-- | The empty pure signature.
emptySignaturePure :: SignaturePure
emptySignaturePure = Signature S.empty emptyMaudeSig

-- Instances
------------

deriving instance Eq       SignaturePure
deriving instance Ord      SignaturePure
deriving instance Show     SignaturePure

instance Binary SignaturePure where
    put sig = put (L.get sigUniqueInsts sig)
              >> put (L.get sigMaudeInfo sig)
    get     = Signature <$> get <*> get

instance NFData SignaturePure where
  rnf (Signature x y) = rnf x `seq` rnf y

------------------------------------------------------------------------------
-- Signatures with an attached Maude process
------------------------------------------------------------------------------

-- | A 'Signature' with an associated, running Maude process.
type SignatureWithMaude = Signature MaudeHandle


-- | Access the facts that are declared as globally fresh.
sigmUniqueInsts :: SignatureWithMaude -> S.Set FactTag
sigmUniqueInsts = L.get sigUniqueInsts

-- | Access the maude handle in a signature.
sigmMaudeHandle :: SignatureWithMaude -> MaudeHandle
sigmMaudeHandle = L.get sigMaudeInfo

-- | Ensure that maude is running and configured with the current signature.
toSignatureWithMaude :: FilePath            -- ^ Path to Maude executable.
                     -> SignaturePure
                     -> IO (SignatureWithMaude)
toSignatureWithMaude maudePath sig = do
    hnd <- startMaude maudePath (L.get sigMaudeInfo sig)
    return $ sig { _sigMaudeInfo = hnd }


-- | The pure signature of a 'SignatureWithMaude'.
toSignaturePure :: SignatureWithMaude -> SignaturePure
toSignaturePure sig = sig { _sigMaudeInfo = mhMaudeSig $ L.get sigMaudeInfo sig }

{- TODO: There should be a finalizer in place such that as soon as the
   MaudeHandle is garbage collected, the appropriate command is sent to Maude

  The code below is a crutch and leads to unnecessary complication.

 
-- | Stop the maude process. This operation is unsafe, as there still might be
-- thunks that rely on the MaudeHandle to refer to a running Maude process.
unsafeStopMaude :: SignatureWithMaude -> IO (SignaturePure)
unsafeStopMaude = error "unsafeStopMaude: implement"

-- | Run an IO action with maude running and configured with a specific
-- signature. As there must not be any part of the return value that depends
-- on unevaluated calls to the Maude process provided to the inner IO action.
unsafeWithMaude :: FilePath      -- ^ Path to Maude executable
                -> SignaturePure -- ^ Signature to use
                -> (SignatureWithMaude -> IO a) -> IO a
unsafeWithMaude maudePath sig  =
    bracket (startMaude maudePath sig) unsafeStopMaude 

-}

-- Instances
------------

instance Eq SignatureWithMaude where
  x == y = toSignaturePure x == toSignaturePure y

instance Ord SignatureWithMaude where
  compare x y = compare (toSignaturePure x) (toSignaturePure y)

instance Show SignatureWithMaude where
  show = show . toSignaturePure

instance Binary SignatureWithMaude where
    put sig@(Signature _ maude) = do
        put (mhFilePath maude)
        put (toSignaturePure sig)
    -- FIXME: reload the right signature
    get = unsafePerformIO <$> (toSignatureWithMaude <$> get <*> get)

instance NFData SignatureWithMaude where
  rnf (Signature x _maude) = rnf x

------------------------------------------------------------------------------
-- Pretty-printing
------------------------------------------------------------------------------

-- | Pretty-print a signature.
prettySignature :: HighlightDocument d => Signature a -> d
prettySignature sig = foldr ($--$) emptyDoc $ map combine  
  [ ("unique_insts",  ppGFresh $ S.toList $ _sigUniqueInsts sig)
  ]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppGFresh = fsep . punctuate comma . map (text . showFactTagArity)
    

