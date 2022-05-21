{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
module Scratch where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import ModelChecking1 (TransitionSystem)

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
var v state = state ! v

val :: val -> Expr var val
val x state = x

(=:) :: Ord var => var -> Expr var val -> Stmt var val -- Effect var val
x =: e = Modify $ \state -> insert x (e state) state
infix 0 =:

(!<=) :: Ord val => Expr var val -> Expr var val -> StatePredicate var val
(e1 !<= e2) state = e1 state <= e2 state

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

-- int fact(int i) {
--   int j = 1;
--   while (i > 1) {
--     j *= i;
--     i -= 1;
--   }
--   return j;
-- }
fact :: Int -> Prog IJ Int
fact i = Vec.fromList
  [ I =: val i
  , J =: val 1
  , CondBranch (var I !<= val 1) 6
  , J =: var J !* var I
  , I =: var I !- val 1
  , goto 2
  , goto 6 -- halt
  ]

data ProgProp loc ap = ProgAtLoc loc | ProgStateProp ap
  deriving (Show, Eq, Ord)

progToTS :: [ap] 
         -> (ap -> StatePredicate var val) 
         -> Prog var val 
         -> TransitionSystem (loc, State var val) loc (ProgProp loc ap)
progToTS aps apToPred prog = undefined