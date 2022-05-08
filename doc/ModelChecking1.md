---
title: "Model Checking in Haskell, Part 1: Transition Systems and
  Invariants"
---

-   [[1]{.toc-section-number} Overview](#overview)
-   [[2]{.toc-section-number} Transition systems](#transition-systems)
-   [[3]{.toc-section-number} Propositions](#propositions)
-   [[4]{.toc-section-number} Checking invariants](#checking-invariants)
-   [[5]{.toc-section-number} Example: Traffic
    light](#example-traffic-light)
-   [[6]{.toc-section-number} Conclusion](#conclusion)

Recently, I've been reading a
[book](https://www.amazon.com/Principles-Model-Checking-MIT-Press/dp/026202649X/ref=sr_1_1?crid=2RGC1B0N79HIJ&keywords=principles+of+model+checking&qid=1651762001&sprefix=principles+of+model+checking%2Caps%2C134&sr=8-1)
and watching a [lecture
series](https://www.youtube.com/watch?v=Y5Hg4MvUXc4&list=PLwabKnOFhE38C0o6z_bhlF_uOUlblDTjh)
about model checking. This is a topic I've learned a bit about in the
past, but never really studied in earnest.

In model checking, we create a *model* of some sort of stateful
artifact, like a computer program, sequential circuit, or even something
in the "real world" (like a vending machine or traffic light). Then, we
state a *property* we would like to hold about *all possible behaviors*
of the model. Finally, we check whether this property holds for the
model, using a variety of nifty algorithms.

This series of blog posts is an attempt to formalize some of the core
notions and algorithms of model checking in Haskell. I hope it provides
a brief and illustrative introduction for other Haskell programmers who
are curious about the topic.

This post is a [literate haskell
document](https://github.com/benjaminselfridge/model-checking/blob/master/src/ModelChecking1.lhs).

Preamble:

``` {.haskell .literate}
module ModelChecking1 where

import Data.List (nubBy, find)
import Prelude hiding (not)
import qualified Prelude as P
```

# Overview

In this post, I will introduce the notion of a transition system, and we
will state simple properties about them, called *invariants*. We will
also implement a simple model checking algorithm, whose aim is to check
that an invariant holds for all reachable states of the system.

# Transition systems

So, what are these "models" we are checking? They are called *transition
systems*. A transition system is a directed graph, where the vertices of
the graph represent possible program states, and the edges represent
transitions from one state to another. The transitions are followed
nondeterministically; when a state has multiple outgoing transitions,
that simply means that it can follow any of them. A transition system
also has a nonempty set of *initial states*, which are the states that
the system may start in.

As we transition from one state to another (by following one of the
edges), certain things may become true or false. We model this with a
set of *atomic propositional variables* which are either true or false
in every state. In Haskell, we represent this set of variables as a type
(or a type variable `ap`), and we formalize the notion of a *truth
assignment* as a function from this type to `Bool`:

``` {.haskell .literate}
type TruthAssignment ap = ap -> Bool
```

The idea is that each state in our transition system is *labeled* with a
truth assignment, identifying which atomic propositions hold. We can now
define a transition system in Haskell:

``` {.haskell .literate}
data TransitionSystem s action ap = TransitionSystem
```

A transition system is a set of *initial* states,

``` {.haskell .literate}
  { tsInitialStates :: [s]
```

a *labeling* of each state with a truth assignment,

``` {.haskell .literate}
  , tsLabel :: s -> TruthAssignment ap
```

and a list of outgoing transitions for each state.

``` {.haskell .literate}
  , tsTransitions :: s -> [(action, s)]
  }
```

For each transition `(action, s')`, `s'` is the next state, and `action`
is a name (not necessarily unique) for the transition. The `action` will
not be used in this post other than as a convenient way to label the
transitions, but it will be more useful in subsequent posts.

# Propositions

The whole point of model checking is to determine whether a transition
system satisfies a given property. In order to to state such a property,
we will need the notion of a logical proposition. I formalize this as a
function that maps `TruthAssignment`s to `Bool`s; the idea is that for a
fixed `TruthAssignment`, a proposition either holds or does not hold.

``` {.haskell .literate}
type Proposition ap = TruthAssignment ap -> Bool
```

With this type, we can define propositional satisfaction as function
application:

``` {.haskell .literate}
(|=) :: TruthAssignment ap -> Proposition ap -> Bool
f |= p = p f
```

If `f` is an assignment and `p` is a proposition, `f |= p` is read as "f
satisfies p".

A very simple proposition is `true`, which holds for all assignments:

``` {.haskell .literate}
true :: Proposition ap
true _ = True
```

Similarly, `false` holds for no assignments:

``` {.haskell .literate}
false :: Proposition ap
false _ = False
```

Given an atomic propositional variable `p`, we can form the proposition
"`p` holds" as follows:

``` {.haskell .literate}
atom :: ap -> Proposition ap
atom ap f = f ap
```

For an assignment `f : ap -> Bool`, `atom ap f` will be `True` if and
only if `f` assigns variable `ap` to `True`.

We can define the usual boolean operators on propositions in terms of
satisfaction:

``` {.haskell .literate}
(.&) :: Proposition ap -> Proposition ap -> Proposition ap
(p .& q) f = (f |= p) && (f |= q)

(.|) :: Proposition ap -> Proposition ap -> Proposition ap
(p .| q) f = (f |= p) || (f |= q)

not :: Proposition ap -> Proposition ap
not p f = P.not (f |= p)

(.->) :: Proposition ap -> Proposition ap -> Proposition ap
p .-> q = not p .| q
```

In other words, the assignment `f` satisfies the proposition `p` and `q`
whenever `f |= p` and `f |= q`; likewise for the other operators.

# Checking invariants

In the previous section, we defined the notion of a truth assignment,
which is a function from variables to truth values. We also defined the
notion of a proposition, which is a property that either holds or does
not holds for a given assignment. Given a transition system `ts` and a
proposition `p`, we can ask: "Does `p` hold at all reachable states in
`ts`?" Stated in terms of the definitions above, we are asking, for each
reachable state `s` of `ts`, whether `tsLabel ts s |= p`. A proposition
which is supposed to hold at all reachable states of a transition system
is called an *invariant*.

So, how do we check whether an invariant holds? The answer is simple: we
search the underlying graph of the transition system, and evaluate the
proposition on each state (more precisely, on the *label* of each
state). To do this, we first define an auxiliary function that collects
all reachable states in the graph, along with a path that leads to each
state, given the start states and a function mapping each state to its
list of possible next states.

``` {.haskell .literate}
reachables :: Eq s => [s] -> (s -> [s]) -> [(s, [s])]
reachables starts = go [] (zip starts (repeat []))
  where go visited [] _ = nubBy (\x y -> fst x == fst y) visited
        go visited starts transitions =
          let nexts = [ (s', s:path)
                      | (s, path) <- starts
                      , s' <- transitions s
                      , s' `notElem` map fst visited ]
          in go (visited ++ starts) nexts transitions
```

Now, to check an invariant, we simply collect all the reachable states
and make sure the invariant holds for each of their labels, producing a
path to a bad state if there is one:

``` {.haskell .literate}
checkInvariant :: Eq s => Proposition ap -> TransitionSystem s action ap -> Maybe [s]
checkInvariant p ts =
  let rs = reachables (tsInitialStates ts) (map snd <$> tsTransitions ts)
  in path <$> find (\(s,_) -> tsLabel ts s |= not p) rs
  where path (s, ss) = reverse (s:ss)
```

# Example: Traffic light

Let's check our first model! The model will be a single traffic light,
and we will make sure that the light is never red and green at the same
time. It's not a very interesting property, but it's a good one for any
traffic light to have.

``` {.haskell .literate}
data Color = Red | Green | Yellow deriving (Show, Eq, Ord)
```

``` {.haskell .literate}
traffic_light :: TransitionSystem Color () Color
traffic_light = TransitionSystem
  { tsInitialStates = [Red]
  , tsLabel = (==)
  , tsTransitions = \s -> case s of
      Red    -> [((), Green )]
      Green  -> [((), Yellow)]
      Yellow -> [((), Red   )]
  }
```

Since the `action` doesn't matter for this example, we just use `()`.
Notice that `Color` serves as both our state type *and* as our set of
atomic propositional variables. The label of each state `s` is `(== s)`,
meaning that only that color is `True`. We can check this in `ghci`:

``` {.haskell}
  > tsLabel traffic_light Red Red     -- is Red true in state Red?
  True
  > tsLabel traffic_light Red Green   -- is Green true in state Red?
  False
  > tsLabel traffic_light Green Green -- is Green true in state Green?
  True
```

Now, we would like to know that `Red` and `Green` are never true at the
same time. It's trivial to see why this is true, because by
construction, there isn't a state in our transition system that
satisfies both `Red` and `Green`.

We can use our `checkInvariant` function to check that our invariant
holds:

``` {.haskell}
  > checkInvariant (not (atom Red .& atom Green)) traffic_light
  Nothing
```

The result `Nothing` means there were no counterexamples, which means
our invariant holds! Let's try it with an invariant that doesn't hold:

``` {.haskell}
  > checkInvariant (not (atom Yellow)) traffic_light
  Just [Red, Green, Yellow]
```

Our invariant checking algorithm was able to find a path to a state that
violated `not (atom Yellow)`; unsurprisingly, the bad state was `Yellow`
(the last state in the counterexample path). Because `Yellow` is
reachable in our transition system, our property doesn't hold. What if,
however, `Yellow` is not reachable?

``` {.haskell}
  > traffic_light = TransitionSystem [Red] (\s -> case s of Red -> [Green]; Green -> [Red]) (==)
  > checkInvariant (not (atom Yellow)) traffic_light
  Nothing
```

# Conclusion

Hopefully, this first post gave you a taste of what model checking is
all about. In the next post, we'll talk about how to convert
higher-level program to transition systems, and use this machinery to
look at a more complex example than the traffic light system studied in
this post.
