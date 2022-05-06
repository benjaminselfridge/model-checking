---
title: "Model Checking in Haskell, Part 2: From Programs to Transition
  Systems"
---

-   [[1]{.toc-section-number} Program Graphs](#program-graphs)
-   [[2]{.toc-section-number} Program Graphs to Transition
    Systems](#program-graphs-to-transition-systems)
-   [[3]{.toc-section-number} Example: Soda
    Machine](#example-soda-machine)

In this post, we'll talk about how to convert an imperative computer
program into a transition system. We'll then look at a few example
programs, and show how to use this conversion to check interesting
invariants about the program's state.

Preamble:

``` {.haskell .literate}
module ModelChecking2 where

import ModelChecking1
import Data.Map.Strict (Map, (!), fromList, adjust)
```

# Program Graphs

Our first task will be to define a very simple imperative programming
language. Our program representation will consist of a set of
*locations*, which can be thought of (roughly) as a line of code in a
language like C. With each such location, we associate a collection of
*guarded transitions*. A guarded transition is a triple
`(guard, effect, loc)`. Intuitively, the idea is: "If `guard` is true of
the current global state, then modify the state with `effect` and go to
location `loc`."

A guarded transition is a directed edge from one program location to
another, which can only be followed when a particular condition holds,
and which, when followed, may change the global program state by
modifying some subset of the global variables. The idea is that when our
program is in a location `loc` while executing, it is allowed to follow
any of `loc`'s outgoing transitions whose guards are satisfied by the
current state of the global variables.

We will call this construction a *program graph*. To define it in
Haskell, we first define a couple auxiliary notions.

The *state* of a program is a mapping from variables to values.

``` {.haskell .literate}
type State var val = Map var val
```

A *guard* is a function that tells us whether the program state
satisfies a particular condition.

``` {.haskell .literate}
type Cond var val = State var val -> Bool
```

Finally, a *program graph* is defined by a set of guarded transitions, a
set of initial locations, and an initial state.

``` {.haskell .literate}
data ProgramGraph loc var val = ProgramGraph
  { pgTransitions :: loc -> [(Cond var val, State var val -> State var val, loc)]
  , pgInitialLocations :: [loc]
  , pgInitialState :: State var val
  }
```

# Program Graphs to Transition Systems

We'd like to check properties of imperative programs using the machinery
developed in the previous post. In order to do that, we first need to
write a function that converts a program graph to a transition system.

``` {.haskell .literate}
pgToTS :: Eq loc
       => ProgramGraph loc var val
       -> TransitionSystem (loc, State var val) (Either loc (Cond var val))
```

For a program graph with locations `loc`, variables `var`, and values
`val`, the states of the corresponding transition system will be pairs
`(loc, State var val)`. In other words, the state of the transition
system has two parts: 1) where we are in the program (the `loc`ation),
and 2) what the concrete `State`s of the global variables are.

The set of atomic propositions will consist of which location we are
currently in, as well as the set of all guards we could possibly define
over the current state. This will allow us to state a very broad class
of properties to check.

Let's walk through the definition of `pgToTS`.

``` {.haskell .literate}
pgToTS pg = TransitionSystem
  { tsInitials = [ (loc, pgInitialState pg)
                 | loc <- pgInitialLocations pg ]
```

The initial states of the transition system will be all pairs
`(loc, state0)` where `l` is an initial location of the program graph,
and `state0` is the initial state of the program graph.

``` {.haskell .literate}
  , tsTransitions = \(loc, state) ->
      [ (loc', action state) | (cond, action, loc') <- pgTransitions pg loc
                             , cond state ]
```

Given a state `(loc, state)` in our transition system, we have an
outgoing transition system for every transition in the program graph
from `loc` whose guard is satisfied by `state`.

``` {.haskell .literate}
  , tsLabel = \(loc, state) c -> case c of
      Left loc' -> loc == loc'
      Right cond -> cond state
  }
```

Finally, each `(loc, state)` pair is is labeled with the proposition
that is `True` for location `loc` and no other locations, and is also
`True` for all conditions that are satisfied by `state`.

# Example: Soda Machine

``` {.haskell .literate}
data SodaMachineVar = NumCoins | NumSodas | NumBeers
  deriving (Show, Eq, Ord)
data SodaMachineLoc = Start | Select
  deriving (Show, Eq)

soda_machine :: Int -> ProgramGraph SodaMachineLoc SodaMachineVar Int
soda_machine max_num_drinks = ProgramGraph
  { pgTransitions = \l -> case l of
      Start -> [ (const True, adjust (+1) NumCoins, Select)
               , (const True, collect_and_refill, Start)
               ]
        where collect_and_refill _ = init
      Select -> [ ( \state -> state ! NumSodas > 0
                  , adjust (subtract 1) NumSodas
                  , Start )
                , ( \state -> state ! NumBeers > 0
                  , adjust (subtract 1) NumBeers
                  , Start )
                ]
  , pgInitialLocations = [Start]
  , pgInitialState = init
  }
 where init = fromList [ (NumCoins, 0)
                       , (NumSodas, max_num_drinks)
                       , (NumBeers, max_num_drinks)
                       ]

soda_machine_invariant_1 :: Int -> Proposition (Either SodaMachineLoc (Cond SodaMachineVar Int))
soda_machine_invariant_1 max_num_drinks f =
  f (Right (\state -> state ! NumCoins ==
                     2*max_num_drinks - (state ! NumSodas + state ! NumBeers)))

soda_machine_invariant_2 :: Int -> Proposition (Either SodaMachineLoc (Cond SodaMachineVar Int))
soda_machine_invariant_2 max_num_drinks =
  atom (Left Start) .-> soda_machine_invariant_1 max_num_drinks
```
