{-# LANGUAGE ViewPatterns #-}
module Main.REPL
  ( REPL
  , REPLProof(..)
  , runREPL
  , loadThy
  , getProofForLemma
  , solve
  , systemAt
  , showMethodsAt
  , showPaths
  , showWith
  ) where

import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import Data.Either (fromLeft)
import qualified Data.Label as L
import qualified Data.Map as M
import Main.TheoryLoader as L (closeTheory, loadTheory, defaultTheoryLoadOptions, maudePath, TheoryLoadError)
import Theory
import Data.Maybe (mapMaybe, fromMaybe)
import Data.List (uncons)
import Control.Monad (guard, void)
import Text.PrettyPrint.Class (render)

type REPL = ReaderT ClosedTheory IO

runREPL :: IO ClosedTheory -> REPL a -> IO a
runREPL thy repl = thy >>= runReaderT repl

maybeREPL :: String -> Maybe a -> REPL a
maybeREPL reason = maybe (fail reason) return

loadThy :: FilePath -> IO ClosedTheory
loadThy inFile = either (error . show) id <$> errOrThy
  where
    errOrThy :: IO (Either TheoryLoadError ClosedTheory)
    errOrThy = runExceptT $ do
      srcThy <- lift $ readFile inFile
      thy    <- fromLeft (error "diff theory") <$> loadTheory defaultTheoryLoadOptions srcThy inFile

      let sig = L.get thySignature thy
      sig'   <- lift $ toSignatureWithMaude (defaultTheoryLoadOptions.maudePath) sig

      fromLeft (error "diff theory") . snd <$> L.closeTheory "" defaultTheoryLoadOptions sig' (Left thy)

type PathMap = M.Map Int (ProofPath, [ProofMethod])

data REPLProof = REPLProof
  { rpProof :: IncrementalProof
  , rpCtxt  :: ProofContext
  , rpPaths :: PathMap }

rankMethods :: ProofContext -> System -> Int -> [ProofMethod]
rankMethods ctxt sys depth =
  let heuristic = fromMaybe (defaultHeuristic False) (L.get pcHeuristic ctxt)
      ranking = useHeuristic heuristic depth
      tactic = fromMaybe [defaultTactic] (L.get pcTactic ctxt)
  in map fst $ rankProofMethods ranking tactic ctxt sys

collectPaths :: ProofContext -> IncrementalProof -> PathMap
collectPaths ctxt prf = M.fromList $ zip [0..] $ map (\p -> (p, getMethods p)) $ go prf
  where
    go :: IncrementalProof -> [ProofPath]
    go (LNode _ cs)
      | M.null cs = [[]]
      | otherwise = concatMap (\(ccn, t) -> map (ccn:) $ go t) $ M.toList cs

    getMethods :: ProofPath -> [ProofMethod]
    getMethods path = fromMaybe (error "illegal path") $ do
      sys <- prf `atPath` path >>= psInfo . root
      return $ rankMethods ctxt sys (length path)

getProofForLemma :: String -> REPL REPLProof
getProofForLemma name = do
  thy <- ask
  let lem = fmap fst $ uncons $ mapMaybe (matcher thy) (L.get thyItems thy)
  maybeREPL "No such lemma" lem
  where
    matcher :: ClosedTheory -> TheoryItem ClosedProtoRule IncrementalProof () -> Maybe REPLProof
    matcher thy (LemmaItem l) = do
      guard (L.get lName l == name)
      let prf = L.get lProof l
      let ctxt = getProofContext l thy
      return $ REPLProof prf ctxt (collectPaths ctxt prf)
    matcher _ _               = Nothing

solve :: Int -> Int -> REPLProof -> REPL REPLProof
solve pathIdx methodIdx prf = 
  let mPath = M.lookup pathIdx $ rpPaths prf
      iPrf = rpProof prf
      ctxt = rpCtxt prf
  in do
  (path, methods) <- maybeREPL "illegal path index" mPath
  method <- maybeREPL "illegal method index" (methods !?! methodIdx)
  sys <- maybeREPL "illegal path" (iPrf `atPath` path >>= psInfo . root)
  iPrf' <- maybeREPL "applying method failed" $ modifyAtPath (runProver (oneStepProver method) ctxt (length path) sys) path iPrf
  return (REPLProof iPrf' ctxt (collectPaths ctxt iPrf'))
  where
    (!?!) :: [a] -> Int -> Maybe a
    []    !?! _ = Nothing
    (a:_) !?! 0 = Just a
    (_:t) !?! n
      | n < 0 = Nothing
      | otherwise = t !?! (n - 1)

systemAt :: Int -> REPLProof -> REPL System
systemAt pathIdx prf =
  let mPath = M.lookup pathIdx $ rpPaths prf
      iPrf = rpProof prf
  in do
    (path, _) <- maybeREPL "illegal path index" mPath
    maybeREPL "illegal path" (iPrf `atPath` path >>= psInfo . root)

getMethodsAt :: Int -> REPLProof -> REPL [ProofMethod]
getMethodsAt i prf = maybe (fail "illegal index") (return . snd) (M.lookup i $ rpPaths prf)

showMethodsAt :: IO ClosedTheory -> Int -> REPL REPLProof -> IO ()
showMethodsAt thy i m = do
  methods <- runREPL thy (m >>= getMethodsAt i)
  mapM_ printMethod (zip [0..] methods)
  where
    printMethod :: (Int, ProofMethod) -> IO ()
    printMethod (j, method) = putStrLn $ show j ++ ": " ++ render (prettyProofMethod method)

showPaths :: IO ClosedTheory -> REPL REPLProof -> IO ()
showPaths thy m = do
  prf <- runREPL thy m
  printTree $ rpProof prf

printTree :: IncrementalProof -> IO ()
printTree p = do
  _ <- go "" 0 "(root)" p
  putChar '\n'
  where
    go :: String -> Int -> CaseName -> IncrementalProof -> IO Int
    go prefix leafNo (showCn -> cn) (LNode _ cs)
      | M.null cs = do
        putStr $ '\n':prefix ++ cn ++ " (" ++ show leafNo ++ ")"
        return $ leafNo + 1
      | otherwise = do
        putStr $ '\n':prefix ++ cn
        let nextPrefix = map mapChar prefix ++ "+--"
        foldl (step nextPrefix) (return leafNo) (M.toList cs)

    step :: String -> IO Int -> (CaseName, IncrementalProof) -> IO Int
    step prefix mi (cn, prf) = do
      i <- mi
      go prefix i cn prf

    showCn :: CaseName -> String
    showCn "" = "(single case)"
    showCn cn = cn

    mapChar :: Char -> Char
    mapChar '+' = '|'
    mapChar '-' = ' '
    mapChar x   = x

showWith :: IO ClosedTheory -> (a -> IO b) -> REPL a -> IO ()
showWith thy cmd m = do
  repl <- runREPL thy m
  void $ cmd repl
