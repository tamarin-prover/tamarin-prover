module Main.ScratchPad where

import qualified Data.Map as M
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

-- | The theory to debug.
thy = loadThy "examples/ake/dh/NAXOS_eCK.spthy"
-- | Constraint solving steps to apply and on which lemma.
steps = getProofForLemma "eCK_key_secrecy"
  >>= trace "--- starting constraint solving ---"
      solve 0 0  -- simplify
  >>= solve 0 0  -- solve first applicable constraint on simplified constraint system

-- | Pretty-print the tree of constraint systems after having applied all steps
--   above.
paths = showPaths thy steps
-- | Pretty-print the applicable proof methods at the given leaf-index. Leaf
--   indices will be shown when running @paths@ above.
methodsAt i = showMethodsAt thy i steps
-- | Run the debug monad @debugM@ defined below.
debug = showWith thy debugM debugInput

{- Executing @paths steps@ in GHCI will show a visual representation of the
   proof tree after applying the steps specified in @steps@. The paths in the
   tree will be indexed.

  Executing @methodsAt X steps@ will show the available proof methods at the
  path indexed with X. Using the outputs of @paths@ and @methodsAt@ can help
  find the indices required to apply more @solve@ steps in @steps@.
-}

-- | Execute the constraint solving steps defined above, and provide input to
--   debug monad @debugM@ defined below. The returned values will be provided as
--   arguments to @debugM@.
debugInput = do
  prf <- steps
  let ctxt = prf.rpCtxt
  let hnd = ctxt._pcSignature._sigMaudeInfo

  s <- systemAt 0 prf
  return (ctxt, hnd, prf, s)

-- | Use the values returned above to perform debugging.
debugM (_, _, _, s) = do
  putStrLn "The constraint system contains the following annotated nodes"
  mapM_ print (M.keys s._sNodes)
