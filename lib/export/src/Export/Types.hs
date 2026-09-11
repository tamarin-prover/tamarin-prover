-- |
-- Shared result and diagnostic types for exporter backends.
module Export.Types
  ( DiagnosticImpact (..),
    DiagnosticSubject (..),
    ExportDiagnostic (..),
    ExportError (..),
    ExportResult (..),
    ExportException (..),
    Translation (..),
    TranslationContext (..),
    emptyTC,
    emptyTypeEnv,
    exportModule,
    captureExport,
    translationFail,
    translationInvariantFail,
  )
where

import Control.Exception qualified as Exception
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Sapic.Typing
import Text.PrettyPrint.Class (Doc, render)
import Theory (LVar, Predicate)
import Theory.Module (ModuleType (..))

data DiagnosticImpact
  = Informational
  | UntranslatedGoal
  | ChangedAssumptions
  | ChangedProcessSemantics
  deriving (Eq, Ord, Show)

data DiagnosticSubject
  = ProcessSubject
  | LemmaSubject String
  | AxiomSubject String
  | RestrictionSubject String
  | BuiltinSubject String
  deriving (Eq, Ord, Show)

data ExportDiagnostic = ExportDiagnostic
  { diagnosticCode :: String,
    diagnosticImpact :: DiagnosticImpact,
    diagnosticSubject :: DiagnosticSubject,
    diagnosticMessage :: String
  }
  deriving (Eq, Ord, Show)

data ExportError = ExportError
  { exportErrorCode :: String,
    exportErrorMessage :: String
  }
  deriving (Eq, Ord, Show)

data ExportResult = ExportResult
  { exportDocument :: Doc,
    exportDiagnostics :: Seq ExportDiagnostic
  }

data ExportException
  = ExportInputException String
  | ExportInvariantException String
  deriving (Show)

instance Exception.Exception ExportException

translationFail :: String -> a
translationFail = Exception.throw . ExportInputException

translationInvariantFail :: String -> a
translationInvariantFail = Exception.throw . ExportInvariantException

data Translation
  = ProVerif
  | DeepSec
  deriving (Ord, Eq)

exportModule :: Translation -> ModuleType
exportModule ProVerif = ModuleProVerif
exportModule DeepSec = ModuleDeepSec

data TranslationContext = TranslationContext
  { trans :: Translation,
    attackerChannel :: Maybe LVar,
    hasBoundStates :: Bool,
    hasUnboundStates :: Bool,
    predicates :: [Predicate],
    replicationBound :: Int,
    skipReuseLemmas :: Bool,
    skipSourceLemmas :: Bool,
    skipRestrictions :: Bool,
    skipPrecise :: Bool
  }
  deriving (Eq, Ord)

emptyTC :: TranslationContext
emptyTC =
  TranslationContext
    { trans = ProVerif,
      attackerChannel = Nothing,
      hasBoundStates = False,
      hasUnboundStates = False,
      predicates = [],
      replicationBound = 3,
      skipReuseLemmas = False,
      skipSourceLemmas = False,
      skipRestrictions = False,
      skipPrecise = False
    }

emptyTypeEnv :: TypingEnvironment
emptyTypeEnv = TypingEnvironment {vars = Map.empty, events = Map.empty, funs = Map.empty}

captureExport :: Seq.Seq ExportDiagnostic -> IO Doc -> IO (Either ExportError ExportResult)
captureExport diagnostics renderDocument = do
  rendered <- Exception.try renderDocument :: IO (Either Exception.SomeException Doc)
  case rendered of
    Left exception -> pure (Left (exceptionToExportError exception))
    Right document -> do
      forced <-
        Exception.try
          ( Exception.evaluate
              (length (render document) + length (show diagnostics))
          ) :: IO (Either Exception.SomeException Int)
      case forced of
        Left exception -> pure (Left (exceptionToExportError exception))
        Right _ -> pure (Right (ExportResult document diagnostics))
  where
    exceptionToExportError exception =
      case Exception.fromException exception of
        Just (ExportInputException message) -> ExportError "EXP-FATAL-INPUT" message
        Just (ExportInvariantException message) -> ExportError "EXP-FATAL-INVARIANT" message
        Nothing -> ExportError "EXP-FATAL-RENDER" (Exception.displayException exception)
