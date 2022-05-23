{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Scratch where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import ModelChecking1 (TransitionSystem(..), (|=), (.|))
import Data.Void
import Control.Arrow ((>>>))

type State var val = Map var val

type Effect var val = State var val -> State var val

type StatePredicate var val = State var val -> Bool

type LineNumber = Int

data Stmt var val = Modify (Effect var val)
                  | CondBranch (StatePredicate var val) LineNumber

type Prog var val = Vector (Stmt var val)

data IJ = I | J deriving (Show, Eq, Ord)

type Expr var val = State var val -> val

var :: Ord var => var -> Expr var val
var v state = state Map.! v

val :: val -> Expr var val
val x state = x

(=:) :: Ord var => var -> Expr var val -> Effect var val
x =: e = \state -> Map.insert x (e state) state
infix 2 =:

(!<=) :: Ord val => Expr var val -> Expr var val -> StatePredicate var val
(e1 !<= e2) state = e1 state <= e2 state
infix 4 !<=

(!==) :: Eq val => Expr var val -> Expr var val -> StatePredicate var val
(e1 !== e2) state = e1 state == e2 state
infix 4 !==

(!*) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 !* e2) state = e1 state * e2 state
infixl 7 !*

(!-) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 !- e2) state = e1 state - e2 state
infixl 6 !-

unconditionally :: StatePredicate var val
unconditionally = const True

goto :: Int -> Stmt var val
goto = CondBranch unconditionally

noop :: Stmt var val
noop = Modify id

data ProgProp ap = ProgAtLoc LineNumber | ProgStateProp ap
  deriving (Show, Eq, Ord)

progToTS :: State var val -- ^ Initial state of program
         -> [ap] -- ^ List of every atomic propositional variable
         -> (ap -> StatePredicate var val) -- ^ mapping from APs to state predicates
         -> Prog var val -- ^ Input program
         -> TransitionSystem (LineNumber, State var val) LineNumber (ProgProp ap)
progToTS initialState aps apToPred prog = TransitionSystem
  { tsInitialStates = [(0, initialState)]
  , tsLabel = \(lineNum, state) -> 
      ProgAtLoc lineNum : [ ProgStateProp p | p <- aps, state |= apToPred p]
  , tsTransitions = \(lineNum, state) -> case prog Vec.! lineNum of
      Modify f -> [(lineNum, (lineNum+1, f state))]
      CondBranch p n
        | p state -> [(lineNum, (n, state))]
        | otherwise -> [(lineNum, (lineNum+1, state))]
  }

data ParProgProp ap = ParProgAtLocs (Vector LineNumber) | ParProgStateProp ap
  deriving (Show, Eq, Ord)

progsToTS :: State var val
          -> [ap] -- ^ Every atomic propositional variable
          -> (ap -> StatePredicate var val)
          -> Vector (Prog var val) -- ^ Input programs to execute in parallel
          -> TransitionSystem (Vector LineNumber, State var val) (Int, LineNumber) (ParProgProp ap)
progsToTS initialState aps apToPred progs = TransitionSystem 
  { tsInitialStates = [(Vec.replicate (Vec.length progs) 0, initialState)]
  , tsLabel = \(lineNums, state) ->
      ParProgAtLocs lineNums : [ ParProgStateProp p | p <- aps, state |= apToPred p ]
  , tsTransitions = \(lineNums, state) -> [ t lineNums state i | i <- [0..Vec.length progs-1]]
  }

  where t lineNums state progId = case prog Vec.! lineNum of
            Modify f -> 
              ((progId, lineNum), (lineNums Vec.// [(progId, lineNum+1)], f state))
            CondBranch p lineNum'
              | p state   -> ((progId, lineNum), (lineNums Vec.// [(progId, lineNum')], state))
              | otherwise -> ((progId, lineNum), (lineNums Vec.// [(progId, lineNum+1)], state))
          where prog = progs Vec.! progId
                lineNum = lineNums Vec.! progId

data PetersonVar = X | B1 | B2 deriving (Show, Eq, Ord)

peterson_process_1 :: Prog PetersonVar Bool
peterson_process_1 = Vec.fromList
  [ -- non-critical section
    Modify (X =: val True >>> B1 =: val True)
    -- busy wait
  , CondBranch (var X !== val False .| var B2 !== val False) 3
  , goto 1
    -- critical section
  , Modify (B1 =: val False)
  , goto 0
  ]

peterson_process_2 :: Prog PetersonVar Bool
peterson_process_2 = Vec.fromList
  [ -- non-critical section
    Modify (X =: val False >>> B2 =: val True)
    -- busy wait
  , CondBranch (var X !== val True .| var B1 !== val False) 3
  , goto 1
    -- critical section
  , Modify (B2 =: val False)
  , goto 0
  ]

petersonTS :: TransitionSystem
  (Vector LineNumber, State PetersonVar Bool)
  (Int, LineNumber)
  (ParProgProp Void)
petersonTS = progsToTS initialState [] absurd (Vec.fromList [peterson_process_1, peterson_process_2])
  where initialState = Map.fromList [(X, False), (B1, False), (B2, False)]