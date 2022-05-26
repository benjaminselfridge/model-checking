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
import Control.Applicative (liftA2)
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

Our language will be called `MIG`, which stands for `Modify`/`IfGoto`.
In `MIG`, a program is a sequence of statements. There are two kinds of
statements:

1.  `Modify`: modify the global variable environment (e.g. assign a
    variable to a value)
2.  `IfGoto`: test a condition; if it's true, go to the given line
    number

The *global variable environment*, or just *environment*, is an
assignment of `val`ues to a set of `var`iables. The environment is going
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

Another occasionally useful statement is `noop`, which is implemented as
a `Modify` that doesn't actually do anything:

``` {.haskell .literate}
noop :: Stmt var val
noop = Modify id
```

A `MIG` program is just a `Vector` of statements:

``` {.haskell .literate}
type Prog var val = Vector (Stmt var val)
```

## The `Modify` statement

In this section and the next section, we will define some helper
functions that will make it easier to create readable statements in
`MIG`. In this section, we focus on `Modify`; in the next, we'll look at
`IfGoto`.

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
definition for the variable `y`. In `MIG`, we could write the
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
needing to use an explicit lambda expression that calls `Map.insert`.
Now, we can define the `x_equals_4_y` statement a bit more nicely:

``` {.haskell}
modify_stmt :: Stmt XY Int
modify_stmt = Modify (X .= (\env -> env Map.! Y * 4))
```

This is better. However, the `Expr` we are binding `X` to is still
defined in terms of a lambda expression and an explicit `Map.!`
operator. We can do a bit better still by defining some more functions
to build `Expr`s more cleanly.

If `x :: var` is a variable, we can create a corresponding expression
for `x`. In our representation, the *expression* for `x` will be a
function that simply looks up `x` in the environment and returns its
value.

``` {.haskell .literate}
var :: Ord var => var -> Expr var val
var x env = env Map.! x
```

If `c :: val` is a constant value, we can create a corresponding
expression for `c`. In our representation, the *expression* for `c` will
be a function that ignores the current environment and blindly returns
the value `c`.

``` {.haskell .literate}
val :: val -> Expr var val
val c _ = c
```

``` {.haskell .literate}
class AsExpr a var val where
  asExpr :: a -> Expr var val
```

If `val` is a numeric type, we can lift the usual numeric operators to
expressions. This can actually be accomplished by providing an orphan
`Num` instance for functions:

``` {.haskell .literate}
instance Num b => Num (a -> b) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  (-) = liftA2 (-)
  abs = fmap abs
  signum = fmap signum
  fromInteger = const . fromInteger
  negate = fmap negate
```

Since an `Expr var val` is just a function `Env var val -> val`, this
means that if `val` has a `Num` instance, we have a corresponding
instance for `Expr var val` that behaves in the way we'd expect.

Now, we can rewrite our `int x = y * 4;` statement in a much nicer way:

``` {.haskell}
modify_stmt :: Stmt XY Int
modify_stmt = Modify (X .= var Y * 4)
```

If we have *two* effects that we'd like to perform, one after another,
we can combine them with the following operator:

``` {.haskell .literate}
(>:) :: Effect var val -> Effect var val -> Effect var val
(a >: b) env = b (a env)
infixr 1 >:
```

If `a` and `b` are effects, `a >: b` is the effect which results from
first performing `a`, then performing `b`. This is useful when we wish
to update two variables atomically, i.e. perform both updates in a
single step of the program.

## The `IfGoto` statement

In this section, we'll define a few helper functions to help us write
`IfGoto` statements in a readable way. `IfGoto` takes an *environment
predicate* and a line number as arguments:

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

Ideally the programmer doesn't use explicit `goto`s, but in `MIG` it
will be the only option for affecting control flow in our programs.
Let's assume `label` refers to a specific line number, namely line 17 of
the program. Then we can write the corresponding `IfGoto` statement like
so:

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
enable us to "build up" larger predicates out of smaller ones.

Now, we can implement the C statement `if (x == 1 + y) goto label;` in a
much nicer way:

``` {.haskell}
if_goto_stmt :: Stmt XY Int
if_goto_stmt = IfGoto (var X .== val 1 + var Y) 17
```

## Implementing factorial

To give you a simple example of how to program in this language, let's
implement factorial. We won't do any model checking of this program;
this is merely to give you (the reader) a concrete sense of how programs
can be written in it.

We're going to hand-translate this C function:

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
has three variables: `n`, 'i', and `res`:

``` {.haskell .literate}
data FactVar = N | I | Res deriving (Show, Eq, Ord)
```

Now we're ready to write the `fact` program (line numbers are listed in
comments to the left of each statement):

``` {.haskell .literate}
fact :: Prog FactVar Int
fact = Vec.fromList
  {- 0 -} [ Modify (Res .= val 1 >: I .= val 2)
  {- 1 -} , IfGoto (pnot (var I .<= var N)) 5
  {- 2 -} ,   Modify (Res .= (var Res * var I))
  {- 3 -} ,   Modify (I   .= (var I   + val 1))
  {- 4 -} ,   goto 1
  {- 5 -} , goto 5 -- halt
          ]
```

We don't have a separate `Halt` statement, so we model that with a
`goto` statement that points to itself, infinitely looping.

# Parallel programs

In this section, we will examine the problem of model checking multiple
programs running in parallel, which all have access to the same global
variable environment. We will use the language developed thus far to
express each individual program, and then we will define a function to
convert a *parallel* program (which is just a collection of sequential
programs) into a transition system.

A *parallel program* is just an array of sequential programs with a
shared environment:

``` {.haskell .literate}
type ParProg var val = Vector (Prog var val)
```

We will use the term *process* to denote a sequential program that is
part of a larger parallel program. To "run" a parallel program, we first
start each process at line 0. Then, we arbitrarily pick which process
will execute next, and we execute that process's current statement,
updating the global variable environment and/or that process's current
line number. This type of parallel execution model is called
*interleaving*, because each process advances independently of the
other, and the processes can advance in any order.

## Example: Peterson's mutual exclusion algorithm

Consider two processes, P0 and P1, which are running corresponding
programs. Suppose that each program has a *critical section*, and if P0
and P1 are every both in their critical sections, bad things can happen.
The property that both processes cannot execute their critical sections
simultaneously is called *mutual exclusion*.

Peterson's algorithm is an elegant way to ensure mutual exclusion. It
uses three variables: `Turn`, `Wait0`, and `Wait1`. Intuitively, the
meaning of each variable is as follows:

-   `Turn` is `False` it if is `P0`'s turn to enter its critical
    section, and `True` if it is `P1`s turn.
-   `Wait0` is `True` if `P0` wishes to enter its critical section or is
    currently in its critical section, and `False` otherwise.
-   `Wait1` is `True` if `P1` wishes to enter its critical section or is
    currently in its critical section, and `False` otherwise.

We implement Peterson's algorithm in our language as a parallel program
with two processes. Each process is in an infinite loop, continually
attempting to enter its own critical section. When a process wants to
enter its critical section, it first sets its own `Wait` variable to
`True`, and then it (somewhat counterintuitively) signals that it is the
*other* process's turn. Then, before it enters its own critical section,
it busy-waits until either the other process is not waiting, or its own
turn has arrived.

``` {.haskell .literate}
data PeteVar = Turn | Wait0 | Wait1 deriving (Show, Eq, Ord)
```

``` {.haskell .literate}
pete_0 :: Prog PeteVar Bool
pete_0 = Vec.fromList
  {- 0 -} [ Modify (Wait0 .= val True)
  {- 1 -} , Modify (Turn .= val True)
  {- 2 -} , IfGoto (var Turn .& var Wait1) 2
  {- 3 -} , noop -- CRITICAL SECTION
  {- 4 -} , Modify (Wait0 .= val False)
  {- 5 -} , goto 0
          ]
```

``` {.haskell .literate}
pete_1 :: Prog PeteVar Bool
pete_1 = Vec.fromList
 {- 0 -} [ Modify (Wait1 .= val True)
 {- 1 -} , Modify (Turn .= val False)
 {- 2 -} , IfGoto (pnot (var Turn) .& var Wait0) 2
 {- 3 -} , noop -- CRITICAL SECTION
 {- 4 -} , Modify (Wait1 .= val False)
 {- 5 -} , goto 0
         ]
```

``` {.haskell .literate}
pete :: ParProg PeteVar Bool
pete = Vec.fromList [ pete_0, pete_1 ]
```

It is possible to reason through why this solution works, and even to
write a formal proof that both processes cannot be at line 3
simultaneously. However, by converting this parallel program to a
transition system, we can automatically check that Peterson's algorithm
ensures mutual exclusion. In the next section, we discuss how to perform
this conversion, and then apply it to this algorithm.

## From parallel programs to transition systems

The conversion from a sequential program to a transition system was
straightforward, and the result was entirely deterministic; i.e. every
state in the system had exactly one outgoing transition, corresponding
to executing the current line of the program. For a parallel program,
this is no longer the case, because at any given moment in time, *any*
of the processes might execute their current line.

A state in such a transition system will be a pair
`(Vector LineNumber, Env var val)`. The first element of this pair is a
vector containing the current line number of each individual process.
The second element is the global variable environment. Note that
although we have a separate line number for each process, we do *not*
have a separate environment; each process shares the global variable
environment.

As for sequential programs, the atomic propositions will be defined by
the caller, and will be mapped to predicates about the current state in
the transition system. Also, the `action` will be a pair
`(ProcId, LineNumber)`, indicating that a given transition was performed
by executing a particular line of a particular process.

``` {.haskell .literate}
type ProcId = Int
```

``` {.haskell .literate}
type ParProgState var val = (Vector LineNumber, Env var val)
```

``` {.haskell .literate}
parProgToTS :: [Env var val]
            -> [ap]
            -> (ap -> Predicate (Vector LineNumber, Env var val))
            -> ParProg var val
            -> TransitionSystem (Vector LineNumber, Env var val) (ProcId, LineNumber) ap
parProgToTS initialEnvs aps apToPred parProg = TransitionSystem
```

As for sequential programs, `initialEnvs` is a list of all initial
environments we are considering, `aps` is the complete list of atomic
propositional variables, and `apToPred` maps each atomic propositional
variable to its corresponding state predicate. For each initial
environment provided by the caller, there is a corresponding initial
state in the transition system with every process starting at line 0:

``` {.haskell .literate}
  { tsInitialStates = [(Vec.replicate (Vec.length parProg) 0, env) | env <- initialEnvs]
```

As for sequential programs, states are labeled by the atomic
propositional variables whose corresponding predicates they satisfy:

``` {.haskell .literate}
  , tsLabel = \s -> [ p | p <- aps, s |= apToPred p ]
```

Each state has one outgoing transition for every process in the input
program, corresponding to executing the current line of that particular
process.

``` {.haskell .literate}
  , tsTransitions = \(lineNums, env) ->
      [ t env lineNums procId | procId <- [0..Vec.length parProg-1] ]
  }
  where t env lineNums procId =
          let lineNum = lineNums Vec.! procId
              process = parProg Vec.! procId
          in case process Vec.! lineNum of
            Modify effect ->
              ((procId, lineNum), (lineNums Vec.// [(procId, lineNum+1)], effect env))
            IfGoto p lineNum'
              | env |= p  -> ((procId, lineNum), (lineNums Vec.// [(procId, lineNum' )], env))
              | otherwise -> ((procId, lineNum), (lineNums Vec.// [(procId, lineNum+1)], env))
```

The following predicate is useful for asserting that a particular
process is at a particular line:

``` {.haskell .literate}
data ProcAtLine = ProcAtLine ProcId LineNumber
  deriving (Show, Eq, Ord)
```

``` {.haskell .literate}
allProcAtLine :: ParProg var val -> [ProcAtLine]
allProcAtLine parProg =
  [ ProcAtLine procId lineNum | procId  <- [0..Vec.length parProg - 1]
                              , lineNum <- [0..Vec.length (parProg Vec.! procId) - 1] ]
```

``` {.haskell .literate}
procAtLinePred :: ProcAtLine -> Predicate (ParProgState var val)
procAtLinePred (ProcAtLine procId lineNum) =
  \(lineNums, _) -> lineNums Vec.! procId == lineNum
```

## Checking Peterson's mutex algorithm

``` {.haskell .literate}
peteTS :: TransitionSystem (ParProgState PeteVar Bool) (ProcId, LineNumber) ProcAtLine
peteTS = parProgToTS [initialEnv] (allProcAtLine pete) procAtLinePred pete
  where initialEnv = Map.fromList [ (Turn, False), (Wait0, False), (Wait1, False) ]
```

![Transition system for the `pete`
program](../images/peterson.png){width="100%" height="100%"}

``` {.haskell}
  > checkInvariant (pnot (atom (ProcAtLine 0 2) .& atom (ProcAtLine 1 2))) peteTS
  Nothing
```
