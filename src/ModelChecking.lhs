Introduction to model checking (with Haskell!)
==============================================

Recently, I've been reading a
[book](https://www.amazon.com/Principles-Model-Checking-MIT-Press/dp/026202649X/ref=sr_1_1?crid=2RGC1B0N79HIJ&keywords=principles+of+model+checking&qid=1651762001&sprefix=principles+of+model+checking%2Caps%2C134&sr=8-1)
and watching a [lecture
series](https://www.youtube.com/watch?v=Y5Hg4MvUXc4&list=PLwabKnOFhE38C0o6z_bhlF_uOUlblDTjh)
about model checking. This is a topic I've learned a bit about in the past, but
never really studied in earnest.

This literate haskell document is an attempt to translate some of my learnings
into the world of Haskell. I hope it provides a brief and illustrative
introduction to the topic for other Haskell programmers who are curious about
the topic. This is for learning purposes only; I deliberately avoided putting
any effort into making things efficient. I'm really using Haskell as a
convenient notation to express the ideas.

Preamble:

> module ModelChecking where
>
> import Data.List (union, (\\), nub, find)
> import Prelude hiding (not, (*))
> import qualified Prelude as P

Transition systems
------------------

So, what are the models we are checking? They are called _transition systems_. A
transition system is basically a directed graph, where the vertices of the graph
represent possible program states, and the edges represent transitions from one
state to another. The transitions are followed nondeterministically; when a
state has multiple outgoing transitions, that simply means that it can follow
any of them.

Along with the states (vertices) and transitions (directed edges), a transition
system has one additional ingredient: a set of _atomic propositional variables_
that are either true or false in each state. In Haskell, we represent these
variables as a type (or a type variable `ap`), and we formalize the notion of an
_assignment_ of variables as a function from this type to `Bool`:

> -- | An assignment is an evaluation of a set of boolean variables.
> type Assignment ap = ap -> Bool

It's often convenient to "lift" a propositional variable `p` to the assignment
which sets `p` to `True`, and everything else to `False`, so we define a
function to accomplish this here:

> only :: Eq ap => ap -> Assignment ap
> only = (==)

The idea is that every state in our transition system is *labeled* with an
assignment, identifying which atomic propositions are true or false in each
state. We can now define a transition system in Haskell:

> data TransitionSystem s ap = TransitionSystem
>   { tsInitials :: [s]
>   , tsTransitions :: [(s, s)]
>   , tsLabel :: s -> Assignment ap
>   }

The initial states are represented as a list, the transitions as an association
list (mathematically, a relation), and the labels as a function from states to
`Assignment`s of the atomic propositions `ap`. As stated in the introduction,
this is by no means a good representation if your goal is efficiency; the point
here is to make the concepts as easy to understand as possible.

Propositions
------------

Each state in our transition system has a corresponding variable assignment. The idea is

type Proposition ap = Assignment ap -> Bool

-- | Propositional satisfaction.
(|=) :: Assignment ap -> Proposition ap -> Bool
f |= p = p f

-- | Atomic proposition.
atom :: ap -> Proposition ap
atom ap f = f ap

-- | Conjunction of two propositions.
(.&) :: Proposition ap -> Proposition ap -> Proposition ap
(p .& q) f = (f |= p) && (f |= q)

-- | Disjunction of two propositions.
(.|) :: Proposition ap -> Proposition ap -> Proposition ap
(p .| q) f = (f |= p) || (f |= q)

-- | Propositional negation.
not :: Proposition ap -> Proposition ap
not p f = P.not (f |= p)

-- | Propositional implication.
(.->) :: Proposition ap -> Proposition ap -> Proposition ap
p .-> q = not p .| q

dfs :: Eq s => [s] -> [(s, s)] -> [s]
dfs starts = go [] starts
  where go visited [] _ = nub visited
        go visited starts transitions =
          let nexts = [ s'' | s <- starts, (s', s'') <- transitions, s == s' ] \\ visited
          in go (visited ++ starts) nexts transitions

-- | Check that an invariant holds for a (finite) transition system. This simply
-- does a depth-first search of the transition system, searching for a reachable
-- state that fails to satisfy the invariant.
checkInvariant :: Eq s => Proposition ap -> TransitionSystem s ap -> Maybe s
checkInvariant inv ts =
  find (\s -> P.not (tsLabel ts s |= inv)) (dfs (tsInitials ts) [ (s, s') | (s, s') <- tsTransitions ts ])

ex :: TransitionSystem Int Int
ex = TransitionSystem
  { tsInitials = [0]
  , tsTransitions = [ (x, (x+2) `mod` 9) | x <- [0..8]]
  , tsLabel = only
  }

data NFA q ap = NFA
  { nfaTransitions :: [(q, Proposition ap, q)]
  , nfaInitials :: [q]
  , nfaFinals :: [q]
  }

nextStatesOn :: NFA q ap -> q -> Assignment ap -> [q]
nextStatesOn nfa q f = [ q' | (q, p, q') <- nfaTransitions nfa, f |= p ]

-- | Product of a transition system and an NFA.
(*) :: Eq q
    => TransitionSystem s ap
    -> NFA q ap
    -> TransitionSystem (s, q) q
ts * nfa = TransitionSystem
  { tsTransitions =
      [ ((s, q), (s', q')) | (s, s') <- tsTransitions ts
                           , (q, p, q') <- nfaTransitions nfa
                           , tsLabel ts s' |= p
                           ]
  , tsInitials =
      [ (s, q) | s  <- tsInitials ts
               , q0 <- nfaInitials nfa
               , q  <- nextStatesOn nfa q0 (tsLabel ts s)
               ]
  , tsLabel = \(s, q) -> only q
  }

data Color = Red | Yellow | Green
  deriving (Eq, Show)

traffic_light :: TransitionSystem Color Color
traffic_light = TransitionSystem
  { tsInitials = [Green]
  , tsTransitions = [ (Red, Green), (Green, Yellow)
                    , (Yellow, Red), (Green, Red) ]
  , tsLabel = \color -> only color
  }

yellow_before_red :: NFA Int Color
yellow_before_red = NFA
  { nfaInitials = [0]
  , nfaFinals = [1]
  , nfaTransitions = [ (0, atom Green, 0)
                     , (0, atom Yellow, 1)
                     , (0, atom Red, 2)
                     , (2, atom Yellow, 2)
                     , (2, not (atom Yellow), 0)
                     ]
  }
