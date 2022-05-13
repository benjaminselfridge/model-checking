---
layout: page
title:  "Model Checking in Haskell, Part 1: Transition Systems and Invariants"
categories: haskell mathematics
---

I've been reading a
[book](https://www.amazon.com/Principles-Model-Checking-MIT-Press/dp/026202649X/ref=sr_1_1?crid=2RGC1B0N79HIJ&keywords=principles+of+model+checking&qid=1651762001&sprefix=principles+of+model+checking%2Caps%2C134&sr=8-1)
and watching a [lecture
series](https://www.youtube.com/watch?v=Y5Hg4MvUXc4&list=PLwabKnOFhE38C0o6z_bhlF_uOUlblDTjh)
about model checking. This is a topic I've learned a bit about in the past, but
never really studied in earnest.

In model checking, we create a *model* of some sort of stateful artifact, like a
computer program, sequential circuit, or even something in the "real world"
(like a vending machine or traffic light). Then, we state a *property* we would
like to hold about *all possible behaviors* of the model. Finally, we check
whether this property holds for the model, using a variety of nifty algorithms.

This series of blog posts constitutes a brief and very high-level introduction
to model checking, using Haskell code to express the ideas and implement the
algorithms. The intended audience is anyone who knows a bit of Haskell, and who
wants to understand what model checking is all about.

This post was generated with `pandoc` from a [literate haskell
document](https://github.com/benjaminselfridge/model-checking/blob/master/src/ModelChecking1.lhs).

Preamble:

> module ModelChecking1 where
>
> import Data.List (nubBy, find)
> import Data.Word
> import System.Random (RandomGen, randomR)

Overview
--------

In this post, we will introduce the notion of a transition system, and we will
state simple properties about them, called *invariants*. We will also implement
a simple model checking algorithm, whose aim is to check that an invariant holds
for all reachable states of the system.

Transition systems
------------------

Let `s`, `action`, and `ap` be arbitrary Haskell types. Then a *transition
system* over state set `s`, action set `action`, and atomic propositions `ap` is
defined as follows:

> data TransitionSystem s action ap = TransitionSystem
>   { tsInitialStates :: [s]
>   , tsLabel         :: s -> [ap]
>   , tsTransitions   :: s -> [(action, s)]
>   }

The intuition behind each of the three fields of a transition system `ts` is as
follows:

* `tsInitialStates ts`: "the states that the system can start in"
* `tsLabel ts s`: "the set of all atomic propositions that are true in state `s`"
* `tsTransitions ts s`: "all of `s`'s outgoing transitions"

The label of a state is an abstraction of the "internal data" of that state, and
the transitions are an abstraction of control flow. Here, a transition is a pair
`(action, s')` where `s'` is the destination state of the transition, and
`action` is a name for the transition.

Example: Traffic light
----------------------

We can create a very simple transition system representing the states and
transitions of a traffic light. The states `s` will be the colors red, yellow,
and green:

> data Color = Red | Yellow | Green deriving (Show, Eq, Ord)

There will only be one action:

> data ChangeColor = ChangeColor deriving (Show, Eq, Ord)

Finally, our set of transitions will allow `Red` to transition to `Green`,
`Green` to `Yellow`, and `Yellow` to `Red`:

> traffic_light :: TransitionSystem Color ChangeColor Color
> traffic_light = TransitionSystem
>   { tsInitialStates = [Red]
>   , tsLabel = \s -> [s]
>   , tsTransitions = \s -> case s of
>       Red    -> [(ChangeColor, Green )]
>       Green  -> [(ChangeColor, Yellow)]
>       Yellow -> [(ChangeColor, Red   )]
>   }

Notice that we reuse our state type `Color` as our set of atomic propositions.
The label of each state `s` is `[s]`: the only color that is on in state `s` is
`s` itself. We can check this in `ghci`:

``` {.haskell}
  > tsLabel traffic_light Red
  [Red]
  > tsLabel traffic_light Yellow
  [Yellow]
  > tsLabel traffic_light Green
  [Green]
```

"Running" a transition system
-----------------------------

A *run* of a transition system is a finite or infinite path in the underlying
graph:

> data Path s action = Path s [(action, s)]
>   deriving (Show)

In the transitions systems we'll define, it will be useful to be able to examine
random infinite runs of the system to get a feel for what the possibilites are:

> randomRun :: RandomGen g => g -> TransitionSystem s action ap -> Path s action
> randomRun g ts = let (i, g') = randomR (0, length (tsInitialStates ts)) g
>                      s = tsInitialStates ts !! i
>                  in Path s (randomRun' g' s ts)
>   where randomRun' g s ts = let nexts = tsTransitions ts s
>                                 (i, g') = randomR (0, length nexts - 1) g
>                                 (action, s') = nexts !! i
>                             in (action, s') : randomRun' g s' ts

We also define a version of `take` that works on infinite `Path`s, so that we can
easily look at finite prefixes:

> takePath :: Int -> Path s action -> Path s action
> takePath n (Path s transitions) = Path s (take n transitions)

We can put this function to the test on our `traffic_light` example in `ghci`:

```{.haskell}
  > import System.Random
  > g = mkStdGen 0
  > takePath 6 (randomRun g traffic_light)
  Path Red [(ChangeColor,Green),(ChangeColor,Yellow),(ChangeColor,Red),(ChangeColor,Green),(ChangeColor,Yellow),(ChangeColor,Red)]
```

Because each state in `traffic_light` has exactly one outgoing transition, this
is the only run we will ever get. In subsequent posts, we'll look at
nondeterministic transition systems which will return different runs with
different random generators.

The following functions will be useful to have:

> singletonPath :: s -> Path s action
> singletonPath s = Path s []

> consPath :: (s, action) -> Path s action -> Path s action
> consPath (s, action) (Path s' tl) = Path s ((action, s'):tl)

> reversePath :: Path s action -> Path s action
> reversePath (Path s prefix) = go [] s prefix
>   where go suffix s [] = Path s suffix
>         go suffix s ((action, s'):prefix) = go ((action, s):suffix) s' prefix

Propositions
------------

We are interested in checking properties about the states of a transition
system. For this, we will need the notion of a *proposition*:

> type Proposition ap = [ap] -> Bool

The `ap` type represents our atomic propositional variables, and a list `[ap]`
is thought of as "the set of variables that are true". In this sense, a
`Proposition` can represent any logical formula over the variables `ap`.

> (|=) :: [a] -> Proposition a -> Bool
> a |= p = p a
> infix 0 |=

`a |= p` is read as "a satisfies p". A very simple predicate is `true`, which
holds for all inputs:

> true :: Proposition a
> true _ = True

Similarly, `false` holds for no inputs:

> false :: Proposition a
> false _ = False

Given an atomic propositional variable `ap`, we can form the proposition "`ap`
holds" as follows:

> atom :: Eq a => a -> Proposition a
> atom a as = a `elem` as

We can define the usual boolean operators on predicates in terms of
satisfaction:

> (.&) :: Proposition a -> Proposition a -> Proposition a
> (p .& q) a = p a && q a
> infixr 3 .&
>
> (.|) :: Proposition a -> Proposition a -> Proposition a
> (p .| q) a = p a || q a
> infixr 2 .|
>
> pnot :: Proposition a -> Proposition a
> pnot p a = not (p a)
>
> (.->) :: Proposition a -> Proposition a -> Proposition a
> (p .-> q) a = if p a then q a else True
> infixr 1 .->

Checking invariants
-------------------

Given a transition system `ts` and a proposition `p`, we can ask: "Does `p` hold
at all reachable states in `ts`?" A proposition which is supposed to hold at all
reachable states of a transition system is called an *invariant*.

To check whether an invariant holds, we evaluate the proposition on each
reachable state (more precisely, on the *label* of each state). To do this, we
define a lazy breadth-first search of the transition system, which discovers all
reachable states and provides a path to each one it finds. We'll first need a
simple queue data structure:

> type Q a = ([a], [a])

> deq :: Q a -> Maybe (a, Q a)
> deq ([], []) = Nothing
> deq (prefix, a:suffix) = Just (a, (prefix, suffix))
> deq (prefix, []) = deq ([], reverse prefix)

> enqs :: [a] -> Q a -> Q a
> enqs as (prefix, suffix) = (as ++ prefix, suffix)

Now, we can implement a classic breadth-first search:

> bfs :: Eq s => [s] -> (s -> [(action, s)]) -> [(s, Path s action)]
> bfs starts transitions =
>   [ (s, reversePath p) | p@(Path s tl) <- loop [] (singletonPath <$> starts, []) ]
>   where loop visited q
>           | Nothing <- deq q = []
>           | Just (Path s _, q') <- deq q, s `elem` visited = loop visited q'
>           | Just (p@(Path s _), q') <- deq q =
>               let nexts = [ consPath (s', action) p | (action, s') <- transitions s ]
>               in p : loop (s:visited) (enqs nexts q)

Now, to check an invariant, we simply collect all the reachable states via `bfs`
and make sure the invariant holds for each of their labels, producing a path to
a bad state if there is one:

> checkInvariant :: Eq s
>                => Proposition ap
>                -> TransitionSystem s action ap
>                -> Maybe (s, Path s action)
> checkInvariant p ts =
>   let rs = bfs (tsInitialStates ts) (tsTransitions ts)
>   in find (\(s,_) -> tsLabel ts s |= pnot p) rs

Checking a traffic light invariant
----------------------------------

Let's check an invariant of our traffic light system -- that the light is never
red and green at the same time. It's not a very interesting invariant, but it's
a good one for any traffic light to have.

We can use our `checkInvariant` function to check that this invariant holds:

``` {.haskell}
  > checkInvariant (pnot (atom Red .& atom Green)) traffic_light
  Nothing
```

The result `Nothing` means there were no counterexamples, which means our
invariant holds! Let's try it with an invariant that doesn't hold:

``` {.haskell}
  > checkInvariant (pnot (atom Yellow)) traffic_light
  Just (Path Red [(ChangeColor,Green),(ChangeColor,Yellow)])
```

Our invariant checking algorithm was able to find a path to a state that
violated `not (atom Yellow)`; unsurprisingly, the bad state was `Yellow` (the
last state in the counterexample path). Because `Yellow` is reachable in our
transition system, our property doesn't hold. What if, however, `Yellow` is not
reachable?

``` {.haskell}
  > traffic_light = TransitionSystem [Red] (:[]) (\s -> case s of Red -> [(ChangeColor, Green)]; Green -> [(ChangeColor, Red)]; Yellow -> [(ChangeColor, Red)])
  > checkInvariant (pnot (atom Yellow)) traffic_light
  Nothing
```

Conclusion
----------

Hopefully, this first post gave you a taste of what model checking is all about.
In the next post, we'll talk about how to convert higher-level program to
transition systems, and use this machinery to look at a more complex example
than the traffic light system studied in this post.
