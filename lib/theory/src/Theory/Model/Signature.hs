{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Signatures for the terms and multiset rewriting rules used to model and
-- reason about a security protocol.
-- modulo the full Diffie-Hellman equational theory and once modulo AC.
module Theory.Model.Signature
  ( -- * Signature type
    Signature (..),

    -- ** Pure signatures
    SignaturePure,
    emptySignaturePure,

    -- ** Using Maude to handle operations relative to a 'Signature'
    SignatureWithMaude,
    toSignatureWithMaude,
    toSignaturePure,
    joinNDCinSigWMaude,

    -- ** Pretty-printing
    prettySignaturePure,
    prettySignaturePureExcept,
    prettySignatureWithMaude,
  )
where

-- import           Control.Applicative
import Control.DeepSeq
import Data.Binary
import Data.Set qualified as S
import Optics.TH (makeFieldLabelsNoPrefix)
import System.IO.Unsafe (unsafePerformIO)
import Term.LTerm
import Term.Maude.Process (MaudeHandle, mhFilePath, mhMaudeSig, startMaude)
import Term.Maude.Signature (MaudeSig, minimalMaudeSig, prettyMaudeSig, prettyMaudeSigExcept, joinNDCinSig)
import Theory.Text.Pretty

-- | A theory signature.
data Signature a = Signature
  { -- The signature of the message algebra
    maudeInfo :: a
  }

makeFieldLabelsNoPrefix ''Signature

------------------------------------------------------------------------------
-- Pure Signatures
------------------------------------------------------------------------------

-- | A 'Signature' without an associated Maude process.
type SignaturePure = Signature MaudeSig

-- | The empty pure signature.
emptySignaturePure :: Bool -> SignaturePure
emptySignaturePure flag = Signature (minimalMaudeSig flag)

-- Instances
------------

deriving instance Eq SignaturePure

deriving instance Ord SignaturePure

deriving instance Show SignaturePure

instance Binary SignaturePure where
  put sig = put sig.maudeInfo
  get = Signature <$> get

instance NFData SignaturePure where
  rnf (Signature y) = rnf y

------------------------------------------------------------------------------
-- Signatures with an attached Maude process
------------------------------------------------------------------------------

-- | A 'Signature' with an associated, running Maude process.
type SignatureWithMaude = Signature MaudeHandle

-- | Ensure that maude is running and configured with the current signature.
toSignatureWithMaude ::
  -- | Path to Maude executable.
  FilePath ->
  SignaturePure ->
  IO (SignatureWithMaude)
toSignatureWithMaude maudePath sig = do
  hnd <- startMaude maudePath sig.maudeInfo
  return $ sig {maudeInfo = hnd}

-- | The pure signature of a 'SignatureWithMaude'.
toSignaturePure :: SignatureWithMaude -> SignaturePure
toSignaturePure sig = sig {maudeInfo = mhMaudeSig sig.maudeInfo}

-- | Adds the given NDC state to a function symbol (by name) in the signature.
joinNDCinSigWMaude :: SignatureWithMaude -> FunSym -> NDCstate -> SignatureWithMaude
joinNDCinSigWMaude sig funSym ndcState = sig {maudeInfo = mh}
  where
    mh = sig.maudeInfo {mhMaudeSig = joinNDCinSig (mhMaudeSig sig.maudeInfo) funSym ndcState}
    


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

-- | Pretty-print a pure signature.
prettySignaturePure :: (HighlightDocument d) => SignaturePure -> d
prettySignaturePure sig =
  prettyMaudeSig sig.maudeInfo

-- | Pretty-print a pure signature, but omit given set of
--   function symbols. Used for pretty-printing OpenTheories
--   with typed function declarations
prettySignaturePureExcept :: HighlightDocument d => S.Set UserDefinedSym -> SignaturePure -> d
prettySignaturePureExcept exc sig  =
  prettyMaudeSigExcept sig.maudeInfo exc

-- | Pretty-print a signature with maude.
prettySignatureWithMaude :: (HighlightDocument d) => SignatureWithMaude -> d
prettySignatureWithMaude sig =
  prettyMaudeSig $ mhMaudeSig sig.maudeInfo
