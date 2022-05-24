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
will be implemented as a *shallowly-embedded domain-specific language
(eDSL)* in Haskell; we won't be writing a lexer or parser, and we won't
even be writing an expression or statement evaluator, because
expressions and statements in our language constructs will *themselves*
be functions which directly evaluate and modify (respectively) the
environment.

In our language, a program is a sequence of statements. There are two
kinds of statements:

1.  `Modify`: modify the global variable environment (e.g. assign a
    variable to a value)
2.  `IfGoto`: test a condition; if it's true, go to the given line
    number

The *global variable environment*, or just *environment*, is an
assignment of values to a set of variables. It doesn't particularly
matter what the variables and values are, so we'll abstract them with
type variables `var` and `val`, respectively. The environment is going
to be a `Map` from `var`s to `val`s:

``` {.haskell .literate}
type Env var val = Map var val
```

A statement that modifies the global variable environment is represented
as an *effect*, which is a function taking the old environment to a new
one:

``` {.haskell .literate}
type Effect var val = Env var val -> Env var val
```

A statement that *branches* needs to change the current line number.
We'll use `Int` as a sensible type for our line numbers:

``` {.haskell .literate}
type LineNumber = Int
```

A statement in our language either modifies the current environment, or
conditionally goes to the given line number:

``` {.haskell .literate}
data Stmt var val = Modify (Effect var val)
                  | IfGoto (Predicate (Env var val)) LineNumber
```

To execute a `Modify` statement, we simply apply the `Effect` to the
current environment, thus modifying it, and then go to the next line in
the program. To execute an `IfGoto` statement, we first test the
`Predicate` against the current environment: if the predicate evaluates
to true, then we go to the `LineNumber` indicated; if it is not true,
then we go to the next line in the program.

We'll also need an unconditional `goto` statement. We'll define it as
`IfGoto true`, where `true :: Predicate a` (defined in the previous
post) is the function that always returns `True`:

``` {.haskell .literate}
goto :: LineNumber -> Stmt var val
goto lineNum = IfGoto true lineNum
```

A program is just a `Vector` of statements:

``` {.haskell .literate}
type Prog var val = Vector (Stmt var val)
```

## The `Modify` statement

In this section and the next section, we will define some helper
functions that will make it easier to create readable statements in our
language. In this section, we focus on `Modify`; in the next, we'll look
at `IfGoto`.

The `Modify` constructor takes a single argument, an `Effect`:

``` {.haskell}
Modify :: Effect var val -> Stmt var val
```

Recall that an *effect* is a function that modifies the global variable
environment:

``` {.haskell}
type Effect var val = Env var val -> Env var val
```

In C, we might see a line like this:

``` {.c}
int x = y * 4;
```

The left-hand side of the `=` is a variable, and the right-hand side is
an *expression* that can be evaluated, given an environment that has a
definition for the variable `y`. In our language, we could write the
corresponding `Modify` statement like so:

``` {.haskell}
data XY = X | Y deriving (Show, Eq, Ord)

modify_stmt :: Stmt XY Int
modify_stmt = Modify (\env -> Map.insert X (env Map.! Y * 4) env)
```

The function we passed to `Modify` took the current environment and
modified it by looking up the value of `Y`, adding `4` to it, and
setting `X` equal to the result. This is okay, but it would be much
nicer to write something that looked more like the corresponding C
statement.

To accomplish this, we'll define an *assignment* operator that works on
single variables. The operator will be `.=`, and the syntax

``` {.haskell}
x .= e
```

will mean "evaluate the expression `e` and assign the result to the
variable `x`". A simple way to represent an *expression* is as a
function from the environment to a particular value:

``` {.haskell .literate}
type Expr var val = Env var val -> val
```

Then, the assignment operator can be written as

``` {.haskell .literate}
(.=) :: Ord var => var -> Expr var val -> Effect var val
(x .= e) env = Map.insert x (e env) env
infix 2 .=
```

This allows us to create an `Effect`, which is a function, without
writing an explicit lambda or defining the function in a `let` or
`where` clause. Now, we can define the `x_equals_4_y` statement a bit
more nicely:

``` {.haskell}
modify_stmt :: Stmt XY Int
modify_stmt = Modify (X .= (\env -> env Map.! Y * 4))
```

This is better. However, the `Expr` we are binding `X` to is still
defined in terms of a lambda expression and an explicit `Map.!`
operator. We can do a bit better still by defining some more functions
to build `Expr`s more cleanly. We'll create "atomic" expressions from
variables and values, and combine expressions using numeric operators.
We will also be able to "lift" ordinary functions into our language.
This is made especially easy because we chose a shallow embedding
approach.

If `x :: var` is a variable, we can create a corresponding expression
for `x`. In our representation, the *expression* for `x` will be a
function that simply looks up `x` in the environment and returns its
value. The function `var` "lifts" any variable to its corresponding
expression.

``` {.haskell .literate}
var :: Ord var => var -> Expr var val
var x env = env Map.! x
```

If `c :: val` is a constant value, we can create a corresponding
expression for `c`. In our representation, the *expression* for `c` will
be a function that ignores the current environment and blindly returns
the value `c`. The function `val` "lifts" a constant value to its
corresponding expression.

``` {.haskell .literate}
val :: val -> Expr var val
val c _ = c
```

If `val` is a numeric type, we can lift the usual numeric operators to
expressions:

``` {.haskell .literate}
(.+) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 .+ e2) env = e1 env + e2 env
infixl 6 .+
```

``` {.haskell .literate}
(.-) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 .- e2) env = e1 env - e2 env
infixl 6 .-
```

``` {.haskell .literate}
(.*) :: Num val => Expr var val -> Expr var val -> Expr var val
(e1 .* e2) env = e1 env * e2 env
infixl 7 .*
```

Furthermore, if a function `f : val -> val` transforms values, we can
lift `f` to a function that transforms expressions:

``` {.haskell .literate}
liftFun :: (val -> val) -> Expr var val -> Expr var val
liftFun f e env = f (e env)
```

Now, let's quickly play around in ghci to get a feel:

``` {.haskell}
  > data XY = X | Y deriving (Show, Eq, Ord)
  > :t var X
  var X :: Expr XY val
  > :t (var X .+ val 1) .- var Y
  (var X .+ var 1) .- var Y :: Num val => Expr XY val
  > :t liftFun (+1) (var X)
  liftFun (+1) (var X) :: Num val => Expr XY val
```

To evaluate an expression, we just *apply* it (as a function) to an
environment:

``` {.haskell}
  > import qualified Data.Map as Map
  > (var X .+ val 1) .- var Y $ Map.fromList [(X, 4), (Y, -2)]
  7
  > liftFun (+1) (var X) $ Map.fromList [(X, 4), (Y, -2)]
  5
```

Now, we can rewrite our `int x = y * 4;` statement in a much nicer way:

``` {.haskell}
modify_stmt :: Stmt XY Int
modify_stmt = Modify (X .= var Y .* 4)
```

If we have *two* effects that we'd like to perform, one after another,
we can combine them with the following operator:

``` {.haskell .literate}
(!:) :: Effect var val -> Effect var val -> Effect var val
(a !: b) env = b (a env)
infixr 1 !:
```

If `a` and `b` are effects, `a !: b` is the effect which results from
first performing `a`, then performing `b`.

``` {.haskell}
  > :t X .= var Y !: Y .= var Y .+ val 1
  X .= var Y !: Y .= var Y .+ val 1
    :: Num val => Env XY val -> Env XY val
  > (X .= var Y) !: (Y .= var Y .+ val 1) $ Map.fromList [(X, 1), (Y, 2)]
  fromList [(X,2),(Y,3)]
```

## The `IfGoto` statement

In this section, we'll define a few helper functions to help us write
`IfGoto` statements in a readable way. The `IfGoto` takes an
*environment predicate* and a line number as arguments:

``` {.haskell}
IfGoto :: Predicate (Env var val) -> LineNumber -> Stmt var val
```

Recall from the previous post that a predicate is just a single-argument
function that returns a `Bool`:

``` {.haskell}
type Predicate a = a -> Bool
```

Therefore, a `Predicate (Env var val)` is a function
`Env var val -> Bool`. If this function evaluates to `True` in the
current environment, the line number should change to the value
specified by the second argument of `IfGoto`, the `LineNumber`.

In C, we might see a conditional `goto` statement like this:

``` {.c}
if (x == 1 + y) goto label;
```

Ideally the programmer doesn't use explicit `goto`s, but in our language
it will be the only option for affecting control flow in our programs.
In our language, assuming `label` refers to line 17, we can write the
corresponding `IfGoto` statement like so:

``` {.haskell}
if_goto_stmt :: Stmt XY Int
if_goto_stmt = IfGoto (\env -> env Map.! X == 1 + env Map.! Y) 17
```

The function we passed to `IfGoto` took the current environment, looked
up the values of `X` and `Y`, and tested whether the value of `X` was
equal to `1` plus the value of `Y`. As with `Modify`, we'll write some
helper functions to create these environment predicates in a way that
more closely resembles the original `C` code. The first such function
will be the equality operator, which evaluates two expressions and
determines if they are equal:

``` {.haskell .literate}
(.==) :: Eq val => Expr var val -> Expr var val -> Predicate (Env var val)
(e1 .== e2) env = e1 env == e2 env
infix 4 .==
```

The next functions we'll need are the inequality operators:

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

We can also lift predicates about `val`s to environment predicates by
supplying them with an expression:

``` {.haskell .literate}
liftPred :: Predicate val -> Expr var val -> Predicate (Env var val)
liftPred f e env = f (e env)
```

Also note that we can combine predicates using the boolean operators
`.&`, `.|`, `pnot`, and `.->` as defined in the previous post; these
enable us to "build up" larger predicates out of smaller ones:

``` {.haskell}
  > :t (val 1 .<= var X) .& (var X .<= var Y)
  (val 1 .<= var X) .& (var X .<= var Y)
  :: (Ord val, Num val) => Predicate (Env XY val)
```

Now, we can implement the C statement `if (x == 1 + y) goto label;` in a
much nicer way:

``` {.haskell}
if_goto_stmt :: Stmt XY Int
if_goto_stmt = IfGoto (var X .== val 1 .+ var Y) 17
```

## Implementing factorial

Now, let's implement the factorial function, just to illustrate how the
different language constructs work. We're going to hand-translate this C
function:

``` {.c}
int fact(int n) {
  int i = 2, res = 1;
  while (i <= n) {
    res *= i;
    i += 1;
  }
  return res;
}
```

into a program written in the above, two-statement language. The program
has two variables, `n` and `res`:

``` {.haskell .literate}
data FactVar = N | I | Res deriving (Show, Eq, Ord)
```

Now we're ready to write the `fact` program (line numbers are listed in
comments to the left of each statement):

``` {.haskell .literate}
fact :: Prog FactVar Int
fact = Vec.fromList
  {- 0 -} [ Modify (Res .= val 1 !: I .= val 2)
  {- 1 -} , IfGoto (pnot (var I .<= var N)) 5
  {- 2 -} ,   Modify (Res .= (var Res .* var I))
  {- 3 -} ,   Modify (I   .= (var I   .+ val 1))
  {- 4 -} ,   goto 1
  {- 5 -} , goto 5 -- halt
          ]
```

We don't have a separate `Halt` statement, so we model that with a
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
progToTS :: [Env var val]
         -> [ap]
         -> (ap -> Predicate (LineNumber, Env var val))
         -> Prog var val
         -> TransitionSystem (LineNumber, Env var val) LineNumber ap
progToTS initialEnvs aps apToPred prog = TransitionSystem
```

The first argument to this function, `initialEnvs`, is a list of
possible initial environments for the program. Every program starts at
line `0`. For each initial environment provided by the caller, there is
a corresponding initial state in the transition system that starts the
program at line `0` with that initial environment:

``` {.haskell .literate}
  { tsInitialStates = [ (0, env) | env <- initialEnvs ]
```

Given a state `s :: (LineNumber, Env var val)`, the label of `s` is the
set of all atomic propositional variables (as supplied by the caller)
whose corresponding environment predicate is satisified by `s`:

``` {.haskell .literate}
  , tsLabel = \s -> [ p | p <- aps, s |= apToPred p ]
```

Each state `(lineNum, env) :: (LineNumber, Env var val)` as a single
outgoing transition.

``` {.haskell .literate}
  , tsTransitions = \(lineNum, env) -> case prog Vec.! lineNum of
```

The `Modify` statement transitions to the next line, and modifies the
environment by applying the given effect:

``` {.haskell .literate}
      Modify effect -> [(lineNum, (lineNum+1, effect env))]
```

The `IfGoto` statement tests the environment predicate; if it's true, we
transition to the given line number, and if it's false, we transition to
the next line number. In both cases, the global variable environment is
left unchanged.

``` {.haskell .literate}
      IfGoto p lineNum'
        | p env     -> [(lineNum, (lineNum' , env))]
        | otherwise -> [(lineNum, (lineNum+1, env))]
  }
```

## Atomic propositions

In translating to a transition system, we need to define our set of
atomic propositional variables, which amounts to identifying a few
predicates about our state which we are interested in. We also need to
map each variable to its corresponding predicate when we call
`progToTS`. This map needs to be a function of type
`ap -> Predicate (LineNumber, Env var val)`; that is, our atomic
propositions will denote predicates that take the current line number
into account as well as the global variable environment.

The following "lifting" operators will be nice to have, as they will
enable us to smoothly define such predicates:

``` {.haskell .literate}
liftL :: Predicate a -> Predicate (a, b)
liftL p (a, _) = p a
```

``` {.haskell .literate}
liftR :: Predicate b -> Predicate (a, b)
liftR p (_, b) = p b
```

With these operators, we can lift a predicate about an `Env var val` to
a predicate about a `(LineNumber, Env var val)` pair:

``` {.haskell .literate}
atEnv :: Predicate (Env var val) -> Predicate (a, Env var val)
atEnv = liftR
```

Furthermore, we sometimes will wish to define invariants that only apply
when we are at a specific line number, so the following function will be
useful:

``` {.haskell .literate}
atLine :: LineNumber -> Predicate (LineNumber, a)
atLine lineNum = liftL (== lineNum)
```

## Converting the factorial program to a transition system

In converting a program to a transition system, we first need to choose:

1)  The set of all possible initial environments
2)  The set of all atomic propositional variables
3)  How each atomic propositional variable maps to a *predicate* about
    the current line number and environment

In fact, these are the first three arguments of the `progToTS` function.
The choices we make will depend on what kinds of properties we want to
verify, and what the set of possible starting states we will want to
consider.

For our factorial program, the property we'll be interested in checking
is a loop invariant which will hold at the beginning of the loop.
Whenever the program is at line 1, the following formula should hold:

    Res == factorial(I-1)

In other words, the current value of `Res` should be the "product so
far." We'd also like to check this loop invariant for not just one
particular input value of `n`, but for a range of inputs.

In light of these considerations, we'll making the following respective
choices:

1)  The set of possible initial environments will be the set of all
    environments with `N = i` for all `i` between `1` and some maximum
    integer `n`. (We'll initialize `Res` and `I` to `0` for
    completeness, but we note that their initial values don't matter,
    since the first line of the program sets them both to `1`.)

2)  We will have two types of atomic propositional variables: ones that
    indicate what the current line number is, and ones that indicate
    whether the condition `Res == factorial(I-1)` is true.

3)  We will map the variables described in 2) to the corresponding
    predicates about the current `(LineNumber, Env var val)` state in
    the transition system.

Our atomic propositions will be of the following type:

``` {.haskell .literate}
data FactProp = FactAtLine Int
              | FactResInvariant
  deriving (Show, Eq, Ord)
```

The full set of propositions is `FactResInvariant`, plus `FactAtLine i`
for every line `i` of the `fact` program:

``` {.haskell .literate}
factProps :: [FactProp]
factProps = FactResInvariant : [ FactAtLine i | i <- [0..Vec.length fact] ]
```

We use the following mapping from `FactProp` to state predicates:

``` {.haskell .literate}
factPropPred :: FactProp -> Predicate (LineNumber, Env FactVar Int)
factPropPred (FactAtLine i) = atLine i
factPropPred FactResInvariant =
  atEnv $ var Res .== liftFun factorial (var I .- val 1)
  where factorial n = product [1..n]
```

Now, we define `factTS` in terms of the above:

``` {.haskell .literate}
factTS :: Int -> TransitionSystem (LineNumber, Env FactVar Int) LineNumber FactProp
factTS n = progToTS initialEnvs factProps factPropPred fact
  where initialEnvs = [ Map.fromList [(N, i), (Res, 0), (I, 0)] | i <- [1..n] ]
```

Let's check our loop invariant for `factTS` for all values of `n` from
`1` to `20`:

``` {.haskell}
  > checkInvariant (atom (FactAtLine 1) .-> atom FactResInvariant) 20
  Nothing
```

Here's a nice picture of `factTS` for `n = 4`. Each state's name is
written in the format `lineNum: <n=value, res=value>`:

![Transition system for the `fact` function with input
`n = 4`](../images/fact.png){width="100%" height="100%"}

We can easily check that this invariant holds throughout the program's
execution, for any concrete `n`:

``` {.haskell}
  > checkInvariant (atom FactInvariant) (factTS 4)
  Nothing
  > checkInvariant (atom FactInvariant) (factTS 20)
  Nothing
```

## That's it for sequential programs

Unfortunately, there's not much else to say about `fact`, or about any
deterministic sequential program for that matter. We're not going to be
able to prove anything in general about such a program, because in order
to even convert a program into a transition system, all of the variables
must have concrete values; therefore, "checking an invariant" of this
system will be little more than simulating the program for a particular
input. For instance, suppose we wanted to make sure that at each loop
iteration, `Res * N! == n!`, where `n` is the original input value and
`N` is the current value of the `N` variable. We could certainly do
this:

This is nice, because it doesn't just check that result of the program
is correct; it actually shows that for input `4`, the values of `N` and
`Res` are consistent at every loop iteration. However, it's still deeply
unsatisfying because it doesn't say anything about arbitrary `N`.

This is less of an issue with parallel programs, which are inherently
nondeterministic; therefore, we'll focus on parallel programs and
protocols for the rest of this blog series. In the next section, we'll
look at parallel programs that operate on a shared state, and we'll
model check a simple mutual exclusion protocol.

# Parallel programs

A *parallel program* is just an array of programs:

``` {.haskell .literate}
type ParProg var val = Vector (Prog var val)
```

## Peterson's algorithm

# From parallel programs to transition systems

## Model checking Peterson's algorithm

# Conclusion
