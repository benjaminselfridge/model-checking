{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
module Scratch where

import ModelChecking1
import Control.Applicative (liftA2)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Void
import ModelChecking2 hiding (Stmt(..), Prog, ParProg)

data Stmt var val = Modify (Effect var val)
                  | IfGoto (Predicate (Env var val)) LineNumber
                  | NonDetGoto LineNumber

type Prog var val = Vector (Stmt var val)
type ParProg var val = Vector (Prog var val)

parProgToTS :: [Env var val]
            -> [ap]
            -> (ap -> Predicate (ParProgState var val))
            -> ParProg var val
            -> TransitionSystem (ParProgState var val) (ProcId, LineNumber) ap
parProgToTS initialEnvs aps apToPred parProg = TransitionSystem
  { tsInitialStates = [(Vec.replicate (Vec.length parProg) 0, env) | env <- initialEnvs]
  , tsLabel = \s -> [ p | p <- aps, s |= apToPred p ]
  , tsTransitions = \(lineNums, env) ->
      [ t | procId <- [0..Vec.length parProg-1], t <- ts env lineNums procId ]
  }
  where ts env lineNums procId =
          let lineNum = lineNums Vec.! procId
              process = parProg Vec.! procId
              action = (procId, lineNum)
          in case process Vec.! lineNum of
               Modify effect ->
                 [ (action, (lineNums Vec.// [(procId, lineNum+1)], effect env)) ]
               IfGoto p lineNum'
                 | env |= p  -> [ (action, (lineNums Vec.// [(procId, lineNum' )], env)) ]
                 | otherwise -> [ (action, (lineNums Vec.// [(procId, lineNum+1)], env)) ]
               NonDetGoto lineNum' ->
                 [ (action, (lineNums Vec.// [(procId, lineNum' )], env))
                 , (action, (lineNums Vec.// [(procId, lineNum+1)], env))
                 ]

data CacheControllerState