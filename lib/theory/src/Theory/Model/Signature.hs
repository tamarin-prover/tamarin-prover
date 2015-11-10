{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Signatures for the terms and multiset rewriting rules used to model and
-- reason about a security protocol.
-- modulo the full Diffie-Hellman equational theory and once modulo AC.
module Theory.Model.Signature (

  -- * Signature type
    Signature(..)

  -- ** Pure signatures
  , SignaturePure
  , emptySignaturePure
  , sigpMaudeSig

  -- ** Using Maude to handle operations relative to a 'Signature'
  , SignatureWithMaude
  , toSignatureWithMaude
  , toSignaturePure
  , sigmMaudeHandle

  -- ** Pretty-printing
  , prettySignaturePure
  , prettySignatureWithMaude

  ) where

import           Data.Binary
import qualified Data.Label           as L

-- import           Control.Applicative
import           Control.DeepSeq

import           System.IO.Unsafe     (unsafePerformIO)

import           Term.Maude.Process   (MaudeHandle, mhFilePath, mhMaudeSig, startMaude)
import           Term.Maude.Signature (MaudeSig, minimalMaudeSig, prettyMaudeSig)
import           Theory.Text.Pretty


-- | A theory signature.
data Signature a = Signature
       { -- The signature of the message algebra
         _sigMaudeInfo  :: a
       }

$(L.mkLabels [''Signature])


------------------------------------------------------------------------------
-- Pure Signatures
------------------------------------------------------------------------------

-- | A 'Signature' without an associated Maude process.
type SignaturePure = Signature MaudeSig

-- | Access the maude signature.
sigpMaudeSig:: SignaturePure L.:-> MaudeSig
sigpMaudeSig = sigMaudeInfo

-- | The empty pure signature.
emptySignaturePure :: Bool -> SignaturePure
emptySignaturePure flag = Signature (minimalMaudeSig flag)

-- Instances
------------

deriving instance Eq       SignaturePure
deriving instance Ord      SignaturePure
deriving instance Show     SignaturePure

instance Binary SignaturePure where
    put sig =  put (L.get sigMaudeInfo sig)
    get     = Signature <$> get

instance NFData SignaturePure where
  rnf (Signature y) = rnf y

------------------------------------------------------------------------------
-- Signatures with an attached Maude process
------------------------------------------------------------------------------

-- | A 'Signature' with an associated, running Maude process.
type SignatureWithMaude = Signature MaudeHandle

-- | Access the maude handle in a signature.
sigmMaudeHandle :: SignatureWithMaude L.:-> MaudeHandle
sigmMaudeHandle = sigMaudeInfo

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
    put sig@(Signature maude) = do
        put (mhFilePath maude)
        put (toSignaturePure sig)
    -- FIXME: reload the right signature
    get = unsafePerformIO <$> (toSignatureWithMaude <$> get <*> get)

instance NFData SignatureWithMaude where
  rnf (Signature _maude) = ()

------------------------------------------------------------------------------
-- Pretty-printing
------------------------------------------------------------------------------

-- | Pretty-print a signature with maude.
prettySignaturePure :: HighlightDocument d => SignaturePure -> d
prettySignaturePure sig =
    prettyMaudeSig $ L.get sigpMaudeSig sig

-- | Pretty-print a pure signature.
prettySignatureWithMaude :: HighlightDocument d => SignatureWithMaude -> d
prettySignatureWithMaude sig =
    prettyMaudeSig $ mhMaudeSig $ L.get sigmMaudeHandle sig

