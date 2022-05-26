{-# LANGUAGE FlexibleInstances #-}

module GraphViz where

import ModelChecking1
import ModelChecking2
-- import ModelChecking3

import Control.Monad (void)
import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Attributes.Complete as GV
import Data.Graph.Inductive.Graph (Node)
import Data.List (intercalate)
import Data.Map ((!))
import Data.Maybe (fromJust)
import Data.String
import Data.Vector (Vector, toList)
import qualified Data.Vector as Vec

class ActionLabel l where
  actionLabel :: l -> String

instance ActionLabel Change where
  actionLabel Change = "change"

-- instance ActionLabel SodaMachineAction where
--   actionLabel InsertCoin = "insert coin"
--   actionLabel GetSoda = "get soda"
--   actionLabel GetBeer = "get beer"
--   actionLabel ReturnCoin = "return coin"
--   actionLabel ServiceMachine = "service machine"

instance (ActionLabel a, ActionLabel b) => ActionLabel (Either a b) where
  actionLabel (Left a) = actionLabel a
  actionLabel (Right b) = actionLabel b

instance ActionLabel (Int, LineNumber) where
  actionLabel _ = ""

instance ActionLabel LineNumber where
  actionLabel lineNum = show lineNum

-- instance ActionLabel ProcessAction where
--   actionLabel StartWaiting = "start waiting"
--   actionLabel EnterCrit = "enter crit"
--   actionLabel ExitCrit = "exit crit"

-- instance ActionLabel BookingEvent where
--   actionLabel Scan = "scan"
--   actionLabel Store = "store"
--   actionLabel PrintCmd = "print_cmd"
--   actionLabel Print = "print"

tsDotGraph :: (Ord s, GV.Labellable s, ActionLabel action)
           => TransitionSystem s action ap
           -> GV.DotGraph Node
tsDotGraph ts = GV.graphElemsToDot params nodes edges
  where nodes = [ (i, s) | ((s, _), i) <- zip (dfs (tsInitialStates ts) (tsTransitions ts)) [0..] ]
        edges = [ (i, i', actionLabel action) | (i, s) <- nodes
                                              , (action, s') <- tsTransitions ts s
                                              , let i' = fromJust (lookup s' nodesToIds) ]
        nodesToIds = (\(a, b) -> (b, a)) <$> nodes
        params = GV.nonClusteredParams
          { GV.globalAttributes = [ GV.GraphAttrs [GV.DPI 192.0 ]]
          , GV.fmtEdge = \(_, _, l) ->
              [GV.Label (GV.StrLabel (fromString $ " " ++ l ++ " "))]
          , GV.fmtNode = \(_, s) ->
              let fillColor = if s `elem` tsInitialStates ts
                    then GV.DeepSkyBlue
                    else GV.LightGray
              in [ GV.style GV.filled
                 , GV.fillColor fillColor
                 , GV.toLabel s
                 ]
          }

graphTS :: (Ord s, GV.Labellable s, ActionLabel action) => FilePath -> TransitionSystem s action ap -> IO ()
graphTS path ts = void $ GV.runGraphviz (tsDotGraph ts) GV.Png path

instance GV.Labellable Color where
  toLabelValue = GV.toLabelValue . show

-- instance GV.Labellable (SodaMachineLoc, State SodaMachineVar Int) where
--   toLabelValue (loc, state) = GV.toLabelValue $
--     show loc ++ ": <ncoins=" ++ show (state ! NumCoins)
--              ++   ",nsodas=" ++ show (state ! NumSodas)
--              ++   ",nbeers=" ++ show (state ! NumBeers) ++ ">"

-- instance (GV.Labellable (LineNumber, State IJ Int)) where
--   toLabelValue (lineNum, state) = GV.toLabelValue $
--     show lineNum ++ ": <i=" ++ show (state ! I)
--                  ++   ",j=" ++ show (state ! J) ++ ">"

-- instance GV.Labellable (ProcessLoc, State Lock Bool) where
--   toLabelValue (loc, state) = GV.toLabelValue $
--     show loc ++ ": <lock=" ++ show (state ! Lock) ++ ">"

-- instance GV.Labellable ((ProcessLoc, ProcessLoc), State Lock Bool) where
--   toLabelValue ((loc1, loc2), state) = GV.toLabelValue $
--     "(" ++ show loc1 ++ "," ++ show loc2 ++ "): <lock=" ++ show (state ! Lock) ++ ">"

-- instance GV.Labellable ((ProcessLoc, ProcessLoc), State PetersonVar Bool) where
--   toLabelValue ((loc1, loc2), state) = GV.toLabelValue $
--     "(" ++ show loc1 ++ "," ++ show loc2 ++ "): " ++
--     "<b1=" ++ show (state ! B1) ++ ", " ++
--     "b2=" ++ show (state ! B2) ++ ", " ++
--     "x=" ++ show (state ! X) ++ ">"

-- instance GV.Labellable (Vector LineNumber, State PetersonVar Bool) where
--   toLabelValue (lineNums, state) = GV.toLabelValue $
--     "(" ++ show (lineNums Vec.! 0) ++ "," ++ show (lineNums Vec.! 1) ++ "): " ++
--     "<x=" ++ show (state ! X) ++ ", " ++
--     "b1=" ++ show (state ! B1) ++ ", " ++
--     "b2=" ++ show (state ! B2) ++ ">"

instance GV.Labellable (LineNumber, Env FactVar Int) where
  toLabelValue (lineNum, env) = GV.toLabelValue $
    show lineNum ++ ": " ++
    "<n="  ++ show (env ! N  ) ++ ", " ++
    "i="   ++ show (env ! I  ) ++ ", " ++
    "res=" ++ show (env ! Res) ++ ">"

instance GV.Labellable (ParProgState PeteVar Bool) where
  toLabelValue (lineNums, env) = GV.toLabelValue $
    "(" ++ intercalate "," (show <$> toList lineNums) ++ "): " ++
    "<turn=" ++ show (env ! Turn ) ++ ", " ++
    "wait0=" ++ show (env ! Wait0) ++ ", " ++
    "wait1=" ++ show (env ! Wait1) ++ ">"
