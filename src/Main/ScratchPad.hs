module Main.ScratchPad where

import qualified Data.Label as L
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace
import Main.REPL
import Theory

{- This module meant for playing around with the Tamarin interactive proving
   REPL that can be found in @Main.REPL@. Before you make any changes to this
   file, we suggest running:
    git update-index --assume-unchanged src/Main/ScratchPad.hs

   This command ensures that any changed you make will not be tracked by git.
   You can undo this by running:
    git update-index --no-assume-unchanged src/Main/ScratchPad.hs

   Below is an example how to use the scratchpad. We load the minimal loop
   theory, access one of its lemma, and apply simplify. The @debugInput@
   defines the input to the printing function @debugM@, which prints results to
   the console.
-}

thy = loadThy "examples/loops/Minimal_Loop_Example.spthy"
steps = getProofForLemma "Start_before_Loop"
  >>= trace "--- starting constraint solving ---"
      solve 0 0  -- simplify

paths = showPaths thy
methodsAt = showMethodsAt thy
debug = showWith thy debugM debugInput

{- Executing @paths steps@ in GHCI will show a visual representation of the
   proof tree after applying the steps specified in @steps@. The paths in the
   tree will be indexed.

  Executing @methodsAt X steps@ will show the available proof methods at the
  path indexed with X. Using the outputs of @paths@ and @methodsAt@ can help
  find the indices required to apply more @solve@ steps in @steps@.
-}

debugInput = do
  prf <- steps
  let ctxt = rpCtxt prf
  let hnd = L.get pcMaudeHandle ctxt
  return (ctxt, hnd, prf)

debugM _ = do
  putStrLn "debugging..."
