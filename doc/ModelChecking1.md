---
title: "Model Checking in Haskell, Part 1: Transition Systems and
  Invariants"
---

-   [[1]{.toc-section-number} Overview](#overview)
-   [[2]{.toc-section-number} Transition systems](#transition-systems)
-   [[3]{.toc-section-number} Example: Traffic
    light](#example-traffic-light)
-   [[4]{.toc-section-number} Predicates and
    propositions](#predicates-and-propositions)
-   [[5]{.toc-section-number} Checking invariants](#checking-invariants)
-   [[6]{.toc-section-number} Checking a traffic light
    invariant](#checking-a-traffic-light-invariant)
-   [[7]{.toc-section-number} Conclusion](#conclusion)

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
```

# Overview

In this post, we will introduce the notion of a transition system, and
we will state simple properties about them, called *invariants*. We will
also implement a simple model checking algorithm, whose aim is to check
that an invariant holds for all reachable states of the system.

# Transition systems

Let `s`, `action`, and `ap` be arbitrary Haskell types. Then a
*transition system* over state set `s`, action set `action`, and atomic
propositions `ap` is defined as follows:

``` {.haskell .literate}
data TransitionSystem s action ap = TransitionSystem
  { tsInitialStates :: [s]
  , tsLabel         :: s -> Predicate ap
  , tsTransitions   :: s -> [(action, s)]
  }
```

A `Predicate` is simply a `Bool`ean-valued function:

``` {.haskell .literate}
type Predicate a = a -> Bool
```

Let `ts :: TransitionSystem s action ap` be a transition system, and let
`s :: s` and `ap :: ap`. The intuition behind each of the three fields
of `ts` are:

-   `tsInitialStates ts`: "the states that the system can start in"
-   `tsLabel ts s ap`: "whether `ap` is true in state `s`"
-   `tsTransitions ts s`: "all possible next states after `s`"

The label of a state is an abstraction of the "internal data" of that
state, and the transitions are an abstraction of control flow.

# Example: Traffic light

We can create a very simple transition system representing the states
and transitions of a traffic light. The states `s` will be the colors
red, yellow, and green:

``` {.haskell .literate}
data Color = Red | Green | Yellow deriving (Show, Eq, Ord)
```

We will use `()` for the `action` type in this example. The atomic
propositions `ap` will also be `Color`; this will allow us to ask which
color is on in each state.

Finally, our set of transitions will allow `Red` to transition to
`Green`, `Green` to `Yellow`, and `Yellow` to `Red`:

``` {.haskell .literate}
traffic_light :: TransitionSystem Color () Color
traffic_light = TransitionSystem
  { tsInitialStates = [Red]
  , tsLabel = \s -> (s ==)
  , tsTransitions = \s -> case s of
      Red    -> [((), Green )]
      Green  -> [((), Yellow)]
      Yellow -> [((), Red   )]
  }
```

The label of each state `s` is `(s ==)`: the only color that is on in
state `s` is `s` itself. We can check this in `ghci`:

``` {.haskell}
  > tsLabel traffic_light Red Red     -- is Red on in state Red?
  True
  > tsLabel traffic_light Red Green   -- is Green on in state Red?
  False
  > tsLabel traffic_light Green Green -- is Green on in state Green?
  True
```

# Predicates and propositions

Recall that a *predicate* is any boolean-valued function. We can define
the *satisfaction* operator `|=` as

``` {.haskell .literate}
(|=) :: a -> Predicate a -> Bool
a |= p = p a
infix 0 |=
```

`a |= p` is read as "a satisfies p". A very simple predicate is `true`,
which holds for all inputs:

``` {.haskell .literate}
true :: Predicate a
true _ = True
```

Similarly, `false` holds for no inputs:

``` {.haskell .literate}
false :: Predicate a
false _ = False
```

We can define the usual boolean operators on predicates in terms of
satisfaction:

``` {.haskell .literate}
(.&) :: Predicate a -> Predicate a -> Predicate a
(p .& q) a = (a |= p) && (a |= q)
infixr 3 .&

(.|) :: Predicate a -> Predicate a -> Predicate a
(p .| q) a = (a |= p) || (a |= q)
infixr 2 .|

pnot :: Predicate a -> Predicate a
pnot p a = not (a |= p)

(.->) :: Predicate a -> Predicate a -> Predicate a
(p .-> q) a = if a |= p then a |= q else True
infixr 1 .->
```

In order to state properties about the states in our transition systems,
we will need the notion of a *proposition*. A `Proposition` is a
predicate about predicates:

``` {.haskell .literate}
type Proposition a = Predicate (Predicate a)
```

Given an atomic propositional variable `ap`, we can form the proposition
"`ap` holds" as follows:

``` {.haskell .literate}
atom :: a -> Proposition a
atom ap f = f ap
```

For a predicate `f : ap -> Bool`, `atom ap f` will be `True` if and only
if `f` assigns variable `ap` to `True`. When a transition system is in
state `s`, we can ask whether `tsLabel s |= p`, which is the same as
asking "is `p` true in state `s`?"

# Checking invariants

Given a transition system `ts` and a proposition `p`, we can ask: "Does
`p` hold at all reachable states in `ts`?" A proposition which is
supposed to hold at all reachable states of a transition system is
called an *invariant*.

To check whether an invariant holds, we evaluate the proposition on each
reachable state (more precisely, on the *label* of each state). To do
this, we first define an auxiliary function that collects all reachable
states in the underlying graph, along with a path that leads to each
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
checkInvariant :: Eq s
               => Proposition ap
               -> TransitionSystem s action ap
               -> Maybe [s]
checkInvariant p ts =
  let rs = reachables (tsInitialStates ts) (map snd <$> tsTransitions ts)
  in path <$> find (\(s,_) -> tsLabel ts s |= pnot p) rs
  where path (s, ss) = reverse (s:ss)
```

# Checking a traffic light invariant

Let's check an invariant of our traffic light system -- that the light
is never red and green at the same time. It's not a very interesting
invariant, but it's a good one for any traffic light to have.

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
