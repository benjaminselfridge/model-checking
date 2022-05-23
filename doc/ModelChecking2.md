---
title: "Model Checking in Haskell, Part 2: From Programs to Transition
  Systems"
---

In the [previous post](ModelChecking1.html), we introduced transition
systems, which are directed graphs that capture how the state of a
system can evolve through time. Each state in the graph was labeled with
a *true-set*, the set of all atomic propositions which are true in that
state. We explored how to build logical propositions in terms of the
atomic propositions of the state labels, and how to check that such a
proposition is an *invariant* of the transition system. By using an
off-the-shelf graph search algorithm, we discovered all reachable states
and evaluated the proposition at each state.

In this post, we will take a look at how transition systems can be
derived from computer programs. We will develop a very simple imperative
programming language, and then we will write a function that converts
programs written in this language to transition systems. We'll also look
at a few examples of such programs, and we'll show how to apply our
`checkInvariant` function from the previous post to these examples to
check important properties.

# A simple imperative programming language

``` {.haskell .literate}
module ModelChecking2 where

import ModelChecking1
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Void
```

In this section, we'll define a simple, Turing-complete imperative
language with variable assignments and conditional gotos. The language
will be implemented as a *shallowly embedded domain-specific language
(eDSL)* in Haskell; we won't be writing a lexer or parser, and we won't
even be writing an expression or statement evaluator, because
expressions and statements in our language constructs will *themselves*
be functions which directly evaluate and modify (respectively) the
environment.

In our language, a program is a sequence of commands, each of which does
one of the following two things:

1.  Modify the global variable environment
2.  Test a condition; if it's true, go to the given line number

The *global variable environment*, or just *environment*, is an
assignment of values to a set of variables. It doesn't particularly
matter what the variables and values are, so we'll abstract them with
type variables `var` and `val`, respectively. The environment is going
to be a `Map` from `var`s to `val`s:

``` {.haskell .literate}
type Env var val = Map var val
```

A command that modifies the global variable environment is represented
as an *effect*, which is a function taking the old environment to a new
one:

``` {.haskell .literate}
type Effect var val = Env var val -> Env var val
```

A command that *branches* needs to change the current line number. We'll
use `Int` as a sensible type for our line numbers:

``` {.haskell .literate}
type LineNumber = Int
```

A statement in our language either modifies the current environment, or
conditionally changes the current line number:

``` {.haskell .literate}
data Stmt var val = Modify (Effect var val)
                  | CondGoto (Predicate (Env var val)) LineNumber
```

To execute a `Modify` statement, we simply apply the `Effect` to the
current environment, thus modifying it, and then go to the next line in
the program. To execute a `CondGoto` statement, we first test the
`Predicate` against the current environment: if the predicate evaluates
to true, then we go to the `LineNumber` indicated; if it is not true,
then we go to the next line in the program.

We'll also need an unconditional `goto` statement. We'll define it as
`CondGoto true`, where `true :: Predicate a` is the function that always
returns `True`:

``` {.haskell .literate}
goto :: LineNumber -> Stmt var val
goto lineNum = CondGoto true lineNum
```

A program is just an array (here, a `Vector`) of statements:

``` {.haskell .literate}
type Prog var val = Vector (Stmt var val)
```

## Building effects

In this section, we'll write a few helper functions to create `Effect`s;
in the next one, we'll do the same for `Predicate`s. They will help us
create easy-to-read programs in our language.

Recall that an *effect* is a function that modifies the global variable
environment. Since the `Env` is just a map from variables to values, the
simplest way to modify the environment is to change a single variable's
value. Let's define an *assignment* operator that works on single
variables. The operator will be `.=`, and the syntax

``` {.haskell}
x .= e
```

will mean "assign the value of expression `e` to the variable `x`". A
simple way to represent an *expression* is as a function from the
environment to a particular value:

``` {.haskell .literate}
type Expr var val = Env var val -> val
```

If `x :: var` is a variable, we can use `x` as an expression. In our
representation of expressions, the *expression* `x` will be a function
that simply looks up the variable in the environment.

``` {.haskell .literate}
var :: Ord var => var -> Expr var val
var x state = state Map.! x
```

If `c :: val` is a constant value, we can use `c` as an expression. In
our representation, the *expression* `c` will be a function that ignores
the current state and returns the value `c`.

``` {.haskell .literate}
val :: val -> Expr var val
val c _ = c
```

If `val` is a numeric type, we can build up expressions using numeric
operators:

``` {.haskell .literate}
(.+) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 .+ e2) state = e1 state + e2 state
infixl 6 .+
```

``` {.haskell .literate}
(.-) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 .- e2) state = e1 state - e2 state
infixl 6 .-
```

``` {.haskell .literate}
(.*) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 .* e2) state = e1 state * e2 state
infixl 7 .*
```

Now, let's quickly play around in ghci to get a feel:

``` {.haskell}
  > data XY = X | Y deriving (Show, Eq, Ord)
  > :t var X
  var X :: Expr XY val
  > :t (var X .+ val 1) .- var Y
  (var X .+ var 1) .- var Y :: Num val => Expr XY val
```

To evaluate an expression, just supply it with a concrete environment:

``` {.haskell}
  > import qualified Data.Map as Map
  > (var X .+ val 1) .- var Y $ Map.fromList [(X, 4), (Y, -2)]
  7
```

Now, we can finally define `.=`, our variable assignment operator:

``` {.haskell .literate}
(.=) :: Ord var => var -> Expr var val -> Effect var val
(x .= e) env = Map.insert x (e env) env
infix 2 .=
```

In other words, `x .= e` is the function which, given an environment,
evaluates the expression `e` in that environment to get a value `v`, and
then sets `x`'s value to `v` in the environment. Again, let's check it
out with ghci:

``` {.haskell}
  > :t X .= var Y .* var Y
  X .= var Y .* var Y :: Num val => Effect XY val
  > X .= var Y .* var Y $ Map.fromList [(X, 4), (Y, -2)]
  fromList [(X,-4),(Y,-2)]
```

We can combine two effects with the `>>>` operator (flipped function
composition) from `Control.Arrow`:

``` {.haskell}
  > import Control.Arrow ((>>>))
  > :t (X .= var Y) >>> (Y .= var Y .+ val 1)
  X .= var Y >>> Y .= var Y .+ val 1
    :: Num val => Env XY val -> Env XY val
  > (X .= var Y) >>> (Y .= var Y .+ val 1) $ Map.fromList [(X, 1), (Y, 2)]
  fromList [(X,2),(Y,3)]
```

If `a` and `b` are effects, `a >>> b` is the effect which results from
first performing `a`, then performing `b`.

## Building environment predicates

Recall that our `CondGoto` constructor takes a `Predicate (Env var val)`
as its first argument. This *environment predicate* is a function
`Env var val -> Bool` which, if it evaluates to true in the current
environment, causes the line number to change to the value specified by
the second argument of `CondGoto`.

For the time being, we'll only need a few operators to build up these
predicates. The first will be the equality operator, which evaluates two
expressions and determines if they are equal:

``` {.haskell .literate}
(.==) :: Eq val => Expr var val -> Expr var val -> Predicate (Env var val)
(e1 .== e2) env = e1 env == e2 env
infix 4 .==
```

The next will be the inequality operators:

``` {.haskell .literate}
(.<=) :: Ord val => Expr var val -> Expr var val -> Predicate (Env var val)
(e1 .<= e2) env = e1 env <= e2 env
infix 4 .<=
```

``` {.haskell .literate}
(.<) :: Ord val => Expr var val -> Expr var val -> Predicate (Env var val)
(e1 .< e2) env = e1 env < e2 env
infix 4 .<
```

``` {.haskell .literate}
(.>=) :: Ord val => Expr var val -> Expr var val -> Predicate (Env var val)
(e1 .>= e2) env = e1 env >= e2 env
infix 4 .>=
```

``` {.haskell .literate}
(.>) :: Ord val => Expr var val -> Expr var val -> Predicate (Env var val)
(e1 .> e2) env = e1 env > e2 env
infix 4 .>
```

This is all we're going to need for this post, but it's an easy enough
language to extend whenever we need new effects or environment
predicates.

## An example (sequential) program

Let's use this language to implement the factorial function, just to
illustrate how the different language constructs work.

We're going to hand-translate this C function:

``` {.c}
int fact(int n) {
  int res = 1;
  while (n > 1) {
    res *= n;
    n -= 1;
  }
  return res;
}
```

into a program written in the above, two-statement language. The program
has two variables, `n` and `res`:

``` {.haskell .literate}
data FactVar = N | Res deriving (Show, Eq, Ord)
```

Now we're ready to write the `fact` program (line numbers are listed in
comments to the left of each command):

``` {.haskell .literate}
fact :: Prog FactVar Int
fact = Vec.fromList
  {- 0 -} [ Modify (Res .= val 1)
  {- 1 -} , CondGoto (var N .<= val 1) 5
  {- 2 -} ,   Modify (Res .= var Res .* var N)
  {- 3 -} ,   Modify (N   .= var N   .- val 1)
  {- 4 -} ,   goto 1
  {- 5 -} , goto 5 -- halt
          ]
```

We don't have a separate `Halt` instruction, so we model that with a
`goto` statement that points to itself, infinitely looping.

# From sequential programs to transition systems

In order to model check programs, we'll need to be able to convert a
program into a transition system. The basic idea will be that a state in
the transition system will be a pair `(LineNumber, Env var val)`,
consisting of the current line number and the current values of the
program variables. Each state will have exactly one outgoing transition,
which corresponds to executing the statement at the current line of the
program and then going to the next line to be executed.

The atomic propositional variables will be defined by the caller. The
caller will provide a list of variables, along with a function mapping
each variable to some predicate involving the current line number and
global variable environment. Then, the label of each state will be the
set of variables whose corresponding predicate is true at the current
`(LineNumber, Env var val)` pair.

The `action` type will just be `LineNumber`, corresponding to
"performing the statement at the given line."

``` {.haskell .literate}
progToTS :: Env var val
         -> [ap]
         -> (ap -> Predicate (LineNumber, Env var val))
         -> Prog var val
         -> TransitionSystem (LineNumber, Env var val) LineNumber ap
progToTS initialEnv aps apToPred prog = TransitionSystem
  { tsInitialStates = [(0, initialEnv)]
  , tsLabel = \(lineNum, env) -> [ p | p <- aps, apToPred p (lineNum, env) ]
  , tsTransitions = \(lineNum, env) -> case prog Vec.! lineNum of
      Modify effect -> [(lineNum, (lineNum+1, effect env))]
      CondGoto p lineNum'
        | p env     -> [(lineNum, (lineNum' , env))]
        | otherwise -> [(lineNum, (lineNum+1, env))]
  }
```

To compute the factorial of `4`, we can build the transition system with
an initial environment of `n = 4`. We aren't interested in checking any
properties, just in illustrating what the transition system looks like;
therefore, we'll use `Void` as our set of atomic propositions, since we
don't need any.

``` {.haskell .literate}
factTS :: TransitionSystem (LineNumber, Env FactVar Int) LineNumber Void
factTS = progToTS initialState [] absurd fact
  where initialState = Map.fromList [(N, 4), (Res, 0)]
```

Here's a nice picture of `factTS`. Each state's name is written in the
format `lineNum: <n=value, res=value>`:

![Transition system for the `fact` function with input
`n = 4`](../images/fact.png){width="30%" height="30%"}

# Parallel programs

A *parallel program* is just an array of programs:

``` {.haskell .literate}
type ParProg var val = Vector (Prog var val)
```

## Peterson's algorithm

# From parallel programs to transition systems

## Model checking Peterson's algorithm

# Conclusion
