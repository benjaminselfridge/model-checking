Recently, I've been reading a
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

This series of blog posts is an attempt to formalize some of the core notions
and algorithms of model checking in Haskell. I hope it provides a brief and
illustrative introduction for other Haskell programmers who are curious about
the topic.

This post is a [literate haskell
document](https://github.com/benjaminselfridge/model-checking/blob/master/src/ModelChecking1.lhs).

Preamble:

> module ModelChecking1 where
>
> import Data.List (nubBy, find)
> import Prelude hiding (not)
> import qualified Prelude as P

Overview
========

In this post, I will introduce the notion of a transition system, and we will
state simple properties about them, called *invariants*. We will also implement
a simple model checking algorithm, whose aim is to check that an invariant holds
for all reachable states of the system.

Transition systems
==================

So, what are these "models" we are checking? They are called _transition
systems_. At a high level, a transition system is a model of any entity with a
*mutable state* that we can ask questions about at any given moment in time.
Such questions include:

  * Hold old is Timmy?
  * How many coins and sodas are in the soda machine?
  * What is the value of the variable `x` in this computer program?

Each such question is mapped to a single, boolean-valued *atomic propositional
variable* from some pre-defined set of variables `ap`. Every state of the system
is associated with a *truth assignment*, giving the value of every variable in
that state:

> type TruthAssignment ap = ap -> Bool

A transition system can also change from one state to another, causing the
atomic propositional variables to change in value. In Haskell, we can define a
transition system over a state set `s` and a set of atomic propositional
variables `ap` as follows:

> data TransitionSystem s action ap = TransitionSystem
>   { tsInitialStates :: [s]

a *labeling* of each state with a truth assignment,

>   , tsLabel :: s -> TruthAssignment ap

and a list of outgoing transitions for each state.

>   , tsTransitions :: s -> [(action, s)]
>   }

For a state `s`, and each transition `(action, s')` in `tsTransitions s`, `s'`
is the new state when the transition is followed, and `action` is a name (not
necessarily unique) for the transition. The `action` type variable will be
instantiated to `()` in this post, but it will be more useful in subsequent
posts.

Propositions
============

The whole point of model checking is to determine whether a transition system
satisfies a given property. In order to to state such a property, we will need
the notion of a logical proposition, which is a function from `TruthAssignment`s
to `Bool`s.

> type Proposition ap = TruthAssignment ap -> Bool

With this type, we can define propositional satisfaction as function application:

> (|=) :: TruthAssignment ap -> Proposition ap -> Bool
> f |= p = p f

If `f` is an assignment and `p` is a proposition, `f |= p` is read as "f
satisfies p".

A very simple proposition is `true`, which holds for all assignments:

> true :: Proposition ap
> true _ = True

Similarly, `false` holds for no assignments:

> false :: Proposition ap
> false _ = False

Given an atomic propositional variable `p`, we can form the proposition "`p`
holds" as follows:

> atom :: ap -> Proposition ap
> atom ap f = f ap

For an assignment `f : ap -> Bool`, `atom ap f` will be `True` if and only if
`f` assigns variable `ap` to `True`.

We can define the usual boolean operators on propositions in terms of
satisfaction:

> (.&) :: Proposition ap -> Proposition ap -> Proposition ap
> (p .& q) f = (f |= p) && (f |= q)
>
> (.|) :: Proposition ap -> Proposition ap -> Proposition ap
> (p .| q) f = (f |= p) || (f |= q)
>
> not :: Proposition ap -> Proposition ap
> not p f = P.not (f |= p)
>
> (.->) :: Proposition ap -> Proposition ap -> Proposition ap
> (p .-> q) f = if f |= p then f |= q else True

Checking invariants
===================

Given a transition system `ts` and a proposition `p`, we can ask: "Does `p` hold
at all reachable states in `ts`?" A proposition which is supposed to hold at all
reachable states of a transition system is called an *invariant*.

So, how do we check whether an invariant holds? The answer is simple: we just
evaluate the proposition on each reachable state (more precisely, on the *label*
of each state). To do this, we first define an auxiliary function that collects
all reachable states in the underlying graph, along with a path that leads to
each state, given the start states and a function mapping each state to its list
of possible next states.

> reachables :: Eq s => [s] -> (s -> [s]) -> [(s, [s])]
> reachables starts = go [] (zip starts (repeat []))
>   where go visited [] _ = nubBy (\x y -> fst x == fst y) visited
>         go visited starts transitions =
>           let nexts = [ (s', s:path)
>                       | (s, path) <- starts
>                       , s' <- transitions s
>                       , s' `notElem` map fst visited ]
>           in go (visited ++ starts) nexts transitions

Now, to check an invariant, we simply collect all the reachable states and make
sure the invariant holds for each of their labels, producing a path to a bad
state if there is one:

> checkInvariant :: Eq s => Proposition ap -> TransitionSystem s action ap -> Maybe [s]
> checkInvariant p ts =
>   let rs = reachables (tsInitialStates ts) (map snd <$> tsTransitions ts)
>   in path <$> find (\(s,_) -> tsLabel ts s |= not p) rs
>   where path (s, ss) = reverse (s:ss)

Example: Traffic light
======================

Let's check our first model! The model will be a single traffic light, and we
will make sure that the light is never red and green at the same time. It's not
a very interesting property, but it's a good one for any traffic light to have.

> data Color = Red | Green | Yellow deriving (Show, Eq, Ord)

> traffic_light :: TransitionSystem Color () Color
> traffic_light = TransitionSystem
>   { tsInitialStates = [Red]
>   , tsLabel = (==)
>   , tsTransitions = \s -> case s of
>       Red    -> [((), Green )]
>       Green  -> [((), Yellow)]
>       Yellow -> [((), Red   )]
>   }

Since the `action` doesn't matter for this example, we just use `()`. Notice
that `Color` serves as both our state type *and* as our set of atomic
propositional variables. The label of each state `s` is `(== s)`, meaning that
only that color is `True`. We can check this in `ghci`:

``` {.haskell}
  > tsLabel traffic_light Red Red     -- is Red true in state Red?
  True
  > tsLabel traffic_light Red Green   -- is Green true in state Red?
  False
  > tsLabel traffic_light Green Green -- is Green true in state Green?
  True
```

Now, we would like to know that `Red` and `Green` are never true at the same
time. It's trivial to see why this is true, because by construction, there isn't
a state in our transition system that satisfies both `Red` and `Green`.

We can use our `checkInvariant` function to check that our invariant holds:

``` {.haskell}
  > checkInvariant (not (atom Red .& atom Green)) traffic_light
  Nothing
```

The result `Nothing` means there were no counterexamples, which means our
invariant holds! Let's try it with an invariant that doesn't hold:

``` {.haskell}
  > checkInvariant (not (atom Yellow)) traffic_light
  Just [Red, Green, Yellow]
```

Our invariant checking algorithm was able to find a path to a state that
violated `not (atom Yellow)`; unsurprisingly, the bad state was `Yellow` (the
last state in the counterexample path). Because `Yellow` is reachable in our
transition system, our property doesn't hold. What if, however, `Yellow` is not
reachable?

``` {.haskell}
  > traffic_light = TransitionSystem [Red] (\s -> case s of Red -> [Green]; Green -> [Red]) (==)
  > checkInvariant (not (atom Yellow)) traffic_light
  Nothing
```

Conclusion
==========

Hopefully, this first post gave you a taste of what model checking is all about.
In the next post, we'll talk about how to convert higher-level program to
transition systems, and use this machinery to look at a more complex example
than the traffic light system studied in this post.
