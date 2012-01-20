{-# LANGUAGE TypeSynonymInstances,PatternGuards,FlexibleInstances,DeriveDataTypeable,OverloadedStrings,ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module ProofAssistant where

import ProofVisualization
import ProofTree
import SymbolicDerivationGraph
import RuleParser

import Control.Monad.Trans
import System.Process
import ApplicativeParsec
import System.Environment
import UnifyACMaude
import System.Console.Haskeline

-- import Data.Typeable
-- import System.Console.CmdArgs hiding ( Quiet )

-- ***************************************************************************
-- Main program
-- ***************************************************************************

{-

TODO: implement show realized
      never use solveAssm on a variable or a constant
      how to handle constant atoms? Seems like i cannot add a rule, but they are assumed public
      anyway.
      solve constants directly without a case split
      add history/claim events (required for properties where requested state is not final)
      handle C-c

options:
  rulesfile
  outputdir
  input-tactics-script: load commands from file in batch mode
  output-tactics-script: log commands for replay
                         should also include loaded commands (i.e., how to get where i am after starting ...)
  refresh-command: command for browser refresh
-}

main :: IO ()
main = do
  args <- getArgs
  let rfile = case args of
                [] -> ["nsl_example.rul","dy_rules.rul"]
                _:_ -> args
  (goals,ruleSet) <- readRulesFiles rfile
  let initProofTree = Unexplored (sdgFromGoal (head goals))
  repl goals ruleSet (proofTreeToZipper initProofTree)

data Cmd = ZptCmd String [String] | UICmd String [String]


repl :: [Rule] -> RuleSet -> ZProofTree -> IO ()
repl goals ruleSet zpt0 = do
  showPage zpt0
  appendFile "/tmp/proofs/commands.log" "# started new session\n"
  runInputT defaultSettings (loop (zpt0:[]))
 where
  loop :: [ZProofTree] -> InputT IO ()
  loop [] = error "impossible"
  loop (zpt:hist) = do
    liftIO $ showPage zpt
    mcmd <- getInputLine "> "
    case mcmd of
      Just cmd ->
        withInterrupt $
          handleInterrupt ((liftIO stopMaude) >> loop (zpt:hist))
                          (handleCmd (zpt:hist) cmd)
      Nothing -> loop (zpt:hist)
  handleCmd [] _cmd = error "impossible"
  handleCmd (zpt:hist) cmd = do
    liftIO $ appendFile "/tmp/proofs/commands.log" (cmd++"\n")
    case parse pCmd "" cmd of
      Left err -> do
        outputStrLn $ show err
        loop (zpt:hist)
      Right (ZptCmd zcmd args) -> do
        case lookup zcmd commands of
         Just f -> do
           zpt' <- f args zpt
           if zpt == zpt'
             then loop (zpt:hist)
             else loop (zpt':zpt:hist)                      
         Nothing -> do
           outputStrLn "invalid command"
           loop (zpt:hist)
      -- UI commands
      Right (UICmd "quit" []) -> outputStrLn $ "bye"
      Right (UICmd "goto" [pos]) ->
        case gotoPos (read pos) (root zpt) of
          Just zpt' -> loop (zpt':hist)
          Nothing -> do
            outputStrLn "Invalid position"
            loop (zpt:hist)
      Right (UICmd "goals" []) -> (outputStrLn $ unlines $ map show goals) >> loop (zpt:hist)
      Right (UICmd "prove" [goalName]) ->
        case filter (\r -> rName r == goalName) goals of
          r:_ -> do
            let initProofTree = Unexplored (sdgFromGoal r)
            loop [proofTreeToZipper initProofTree]
          _ -> outputStrLn "invalid goal" >> loop (zpt:hist)
      Right (UICmd "stats" []) -> (outputStrLn $ showProofTreeStats (zipperToProofTree zpt)) >> loop (zpt:hist)
      Right (UICmd "undo" []) ->
       case hist of
         [] -> outputStrLn "no previous step" >> loop (zpt:hist)
         _ -> loop hist
      Right (UICmd "page" []) -> do
        liftIO $ showPage zpt
        loop (zpt:hist)
      Right (UICmd _ _) -> do
        outputStrLn "invalid UI command" >> loop (zpt:hist)
  tacticWrapper tac zpt =
    case tac ruleSet zpt of
      Left s -> do
        outputStrLn $ "Error solving: "++s
        return zpt
      Right zpt' ->
        tryMove (nthUnexplored 0) zpt'
  showPage zpt = do
    zProofTreeToHtmlFile zpt "/tmp/proofs/a.html"
    runCommand ("open -a Safari -g /tmp/proofs/a.html")
  tryMove f zpt =
    case f zpt of
      Just zpt' -> return zpt'
      Nothing -> do
        outputStrLn "cannot move in this direction"
        return zpt
  commands = [("left", \_args -> tryMove left),
              ("right", \_args -> tryMove right),
              ("up", \_args -> tryMove up),
              ("down", \_args -> tryMove downLeft),
              ("nextGoal", \_args -> tryMove nextUnexplored),
              ("nextRealized", \_args -> tryMove nextRealized),
              ("next", \_args -> tryMove next),
              ("goal", \args -> tryMove (nthUnexplored (read (args!!0)))),
              ("prevGoal", \_args -> tryMove prevUnexplored),
              ("prevRealized", \_args -> tryMove prevRealized),
              ("prev", \_args -> tryMove prev),
              ("goto", \args -> tryMove (gotoPos (read (args!!0)))), -- TODO: revover from invalid arguments
              ("solve", \args -> tacticWrapper (\rs azpt -> solveCurrent rs (read (args!!0)) azpt)),
              ("auto", \_args -> tacticWrapper (\rs azpt -> auto rs azpt)),
              ("fullAuto", \_args -> tacticWrapper (\rs azpt -> fullAuto rs azpt)),
              ("step", \_args -> tacticWrapper (\rs azpt -> step rs azpt)),
              ("contradication", \_args -> tacticWrapper (\_rs azpt -> transformCurrent contradictionSDG azpt)),
              ("stepHere", \_args -> tacticWrapper (\rs azpt -> here (step rs) azpt)),
              ("autoHere", \_args -> tacticWrapper (\rs azpt -> here (auto rs) azpt)),
              ("fullSteps", \args -> tacticWrapper (\rs azpt -> iterateRuleUpTo (read (args!!0)) (anywhere (selectFst rs)) azpt)),
              ("steps", \args -> tacticWrapper (\rs azpt -> iterateRuleUpTo (read (args!!0)) (step rs) azpt)),
              ("stepsHere", \args -> tacticWrapper (\rs azpt -> here (iterateRuleUpTo (read (args!!0)) (step rs)) azpt))
             ]


pCmd :: GenParser Char st Cmd
pCmd =
     char ':' *> (UICmd <$> pWord <*> many (pWhiteSpace *> pWord))
     <|> (ZptCmd <$> pWord <*> many (pWhiteSpace *> pWord))
 where
  pWord = many1 (noneOf ": ")
  pWhiteSpace = many1 (char ' ')