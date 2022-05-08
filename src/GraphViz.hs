module GraphViz where

import ModelChecking1
import ModelChecking2
import ModelChecking3

import Control.Monad (void)
import Data.GraphViz
import Data.Graph.Inductive.Graph (Node)
import Data.Map ((!))
import Data.Maybe (fromJust)

tsDotGraph :: (Ord s, Labellable s) => TransitionSystem s ap -> DotGraph Node
tsDotGraph ts = graphElemsToDot quickParams nodes edges
  where nodes = [ (i, s) | ((s, _), i) <- zip (reachables (tsInitials ts) (tsTransitions ts)) [0..] ]
        edges = [ (i, i', "" :: String) | (i, s) <- nodes
                                       , s' <- tsTransitions ts s
                                       , let i' = fromJust (lookup s' nodesToIds) ]
        nodesToIds = (\(a, b) -> (b, a)) <$> nodes

graphTS :: (Ord s, Labellable s) => FilePath -> TransitionSystem s ap -> IO ()
graphTS path ts = void $ runGraphviz (tsDotGraph ts) Png path

instance Labellable (SodaMachineLoc, State SodaMachineVar Int) where
  toLabelValue (loc, state) = toLabelValue $
    show loc ++ ": <ncoins=" ++ show (state ! NumCoins)
             ++   ",nsodas=" ++ show (state ! NumSodas)
             ++   ",nbeers=" ++ show (state ! NumBeers) ++ ">"

instance Labellable (ProcessLoc, State Lock Bool) where
  toLabelValue (loc, state) = toLabelValue $
    show loc ++ ": <lock=" ++ show (state ! Lock) ++ ">"

instance Labellable ((ProcessLoc, ProcessLoc), State Lock Bool) where
  toLabelValue ((loc1, loc2), state) = toLabelValue $
    "(" ++ show loc1 ++ "," ++ show loc2 ++ "): <lock=" ++ show (state ! Lock) ++ ">"
