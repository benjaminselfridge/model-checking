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
document](https://github.com/benjaminselfridge/model-checking/blob/master/src/ModelChecking.lhs).

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
the simplest model checking algorithm, whose aim is to check that an invariant
holds for all reachable states of the system.

Transition systems
==================

So, what are these "models" we are checking? They are called _transition
systems_. A transition system is a directed graph, where the vertices of the
graph represent possible program states, and the edges represent transitions
from one state to another. The transitions are followed nondeterministically;
when a state has multiple outgoing transitions, that simply means that it can
follow any of them. A transition system also has a nonempty set of _initial
states_, which correspond to the beginning of a program's execution.

As we transition from one state to another (by following one of the edges),
certain things may be come true or false. We model this with a set of *atomic
propositional variables*. Each state, then, comes equipped with an *assignment*,
giving the truth value of each one of these variables when the system is in that
particular state. In Haskell, we represent this set of variables as a type (or a
type variable `ap`), and we formalize the notion of an *assignment* of variables
as a function from this type to `Bool`:

> type Assignment ap = ap -> Bool

The idea is that every state in our transition system is *labeled* with an
assignment, identifying which atomic propositions are true or false in each
state. We can now define a transition system in Haskell:

> data TransitionSystem s ap = TransitionSystem
>   { tsInitials :: [s]
>   , tsTransitions :: s -> [s]
>   , tsLabel :: s -> Assignment ap
>   }

The initial states are represented as a list, the transitions as a function
mapping each state to its set of successor states, and the labels as a function
from states to `Assignment`s of the atomic propositions `ap`.

Propositions
============

As stated above, every state in our transition system is "labeled" with an
assignment of boolean truth values to the propositional variables `ap`. We are
interested in checking whether certain properties hold for our transition
system. In order to to state these properties, we will need the notion of a
logical proposition. I formalize this as a function that maps `Assignment`s to
`Bool`s; the idea is that for a fixed `Assignment` of values to the atomic
propositional variables, a proposition either holds or does not hold.

> type Proposition ap = Assignment ap -> Bool

With this type, we can define propositional satisfaction as function application:

> (|=) :: Assignment ap -> Proposition ap -> Bool
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

Given an assignment `f : ap -> Bool`, `atom ap f` will be `True` if and only if
`f` assigns `True` to the atomic propositional variable `ap`.

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
> p .-> q = not p .| q

In other words, the assignment `f` satisfies the proposition `p` and `q`
whenever `f |= p` and `f |= q`; likewise for the other operators.

Checking invariants
===================

In the previous section, we defined the notion of an assignment, which is a
function from variables to truth values, as well as the notion of a proposition,
which either holds or does not hold for a given assignment. We can now ask a
simple question of a given transition system `ts` and a given proposition `p`:
"Does `p` hold at all reachable states in `ts`?" Stated in terms of the
definitions above, we are asking, for each reachable state `s` of `ts`, whether
`tsLabel ts s |= p`.

So, how do we check whether an invariant holds? The answer is simple: we search
the underlying graph of the transition system, and evaluate the proposition on
each state (more precisely, on the *label* of each state). To do this, we first
define an auxiliary function that collects all reachable states in the graph,
along with a path that leads to each state.

> reachables :: Eq s => [s] -> (s -> [s]) -> [(s, [s])]
> reachables starts = go [] (zip starts (repeat []))
>   where go visited [] _ = nubBy (\x y -> fst x == fst y) visited
>         go visited starts transitions =
>           let nexts = [ (s', s:path)  | (s, path) <- starts
>                                       , s' <- transitions s
>                                       , s' `notElem` map fst visited ]
>           in go (visited ++ starts) nexts transitions

Now, to check an invariant, we simply collect all the reachable states and make
sure the invariant holds for each of their labels, producing a path to a bad
state if there is one:

> checkInvariant :: Eq s => Proposition ap -> TransitionSystem s ap -> Maybe [s]
> checkInvariant p ts =
>   let rs = reachables (tsInitials ts) (tsTransitions ts)
>   in path <$> find (\(s,_) -> tsLabel ts s |= not p) rs
>   where path (s, rpath) = reverse (s:rpath)

Let's fire up ghci and check our first model! The model will be a single traffic
light, and we will make sure that the light is never red and green at the same
time. It's not a very interesting property, but it's a good one for any traffic
light to have.

``` {.haskell}
  > data Color = Red | Green | Yellow deriving (Show, Eq)
  > ts = TransitionSystem [Red] (\s -> case s of Red -> [Green]; Green -> [Yellow]; Yellow -> [Red]) (==)
```

In this case, our set of atomic propositions is just `Red`, `Green`, and
`Yellow`, which is the same as our set of states! We can see this by examining
the type of `ts`:

``` {.haskell}
  > :type ts
  ts :: TransitionSystem Color Color
```

The label of each state `s` is `(== s)`, meaning that only that color is `True`.

``` {.haskell}
  > tsLabel ts Red Red     -- is Red true in state Red?
  True
  > tsLabel ts Red Green   -- is Green true in state Red?
  False
  > tsLabel ts Green Green -- is Green true in state Green?
  True
```

Now, we would like to know that `Red` and `Green` are never true at the same
time. It's trivial to see why this is true, because by construction, there isn't
a state in our transition system that satisfies both `Red` and `Green`.

We can use our `checkInvariant` function to check that our invariant holds:

``` {.haskell}
  > checkInvariant (not (atom Red .& atom Green)) ts
  Nothing
```

The result `Nothing` means there were no counterexamples, which means our
invariant holds! Let's try it with an invariant that doesn't hold:

``` {.haskell}
  > checkInvariant (not (atom Yellow)) ts
  Just [Red, Green, Yellow]
```

Our invariant checking algorithm was able to find a path to a state that
violated `not (atom Yellow)`; unsurprisingly, the bad state was `Yellow` (the
last state in the counterexample path). Because `Yellow` is reachable in our
transition system, our property doesn't hold. What if, however, `Yellow` is not
reachable?

``` {.haskell}
  > ts = TransitionSystem [Red] (\s -> case s of Red -> [Green]; Green -> [Red]) (==)
  > checkInvariant (not (atom Yellow)) ts
  Nothing
```

Conclusion
==========

At this point, you're probably thinking: "That's it?" Well, no! That's
definitely not it. There's tons more things to talk about, and we will be
getting deeper into the world of model checking in subsequent posts.

There's two basic dimensions that will become deeper. The first dimension is
about *how* we create a transition system from a more high-level artifact. Many
of the artifacts we're interested in modeling involve multiple, concurrent
processes that interact in interesting ways, and we'll need to expand our
machinery to construct appropriate transition systems in order to succesfully
model these artifacts.

The second dimension involves the kinds of properties we can state. Invariants
are great, but they're *dead* simple. They don't let you talk about how
different states relate to each other, and they also don't let you talk about
eventuality ("at some point in the future, this thing will happen"). In future
posts, we'll explore how to state, and verify, more complex properties of this
sort.

Hopefully, this first post gave you a taste of what model checking is all about.
In the next post, we'll explore the second dimension a little bit by expanding
the kinds of properties we can state and verify. We'll define the notion of a
*regular safety property*, which is a generalization of invariants that allows
us to talk about relationships between states.
