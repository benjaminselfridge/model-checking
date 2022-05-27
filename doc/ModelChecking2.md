---
title: "Model Checking in Haskell, Part 2: From Programs to Transition
  Systems"
---

In the [previous post](ModelChecking1.html), we introduced transition
systems, which are directed graphs that capture properties of the state
of a system as it evolves through time. Each state in the graph was
labeled with a *true-set*, the set of all atomic propositions which are
true in that state. We explored how to build logical propositions in
terms of the atomic propositions of the state labels, and how to check
that such a proposition is an *invariant* of the transition system. By
using an off-the-shelf graph search algorithm, we discovered all
reachable states and evaluated the proposition at each state.

In this post, we will take a look at how transition systems can be
derived from computer programs. We will develop a very simple imperative
programming language, and then we will write a function that converts
parallel programs written in this language to transition systems.
Finally, we'll use this language to implement Peterson's algorithm for
mutual exclusion, and we'll use the `checkInvariant` function from the
previous post to ensure that it is correct.

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
will be implemented as a *embedded domain-specific language (eDSL)* in
Haskell. The embedding will be (mostly) shallow. We will use Haskell
functions to represent modifications to the state of the program
variables and predicates about the state (which affect control flow).
However, we will not allow these functions to modify or query the
current line number in the program; that bit will be deeply embedded in
the language AST.

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

A statement in `MIG` either modifies the current environment, or
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
Now, we can define the `modify_stmt` statement a bit more nicely:

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

Also note that we can combine predicates using the boolean operators
`.&`, `.|`, `pnot`, and `.->` as defined in the previous post; these
enable us to "build up" larger predicates out of smaller ones.

Now, we can implement the C statement `if (x == 1 + y) goto label;` in a
much nicer way:

``` {.haskell}
if_goto_stmt :: Stmt XY Int
if_goto_stmt = IfGoto (var X .== 1 + var Y) 17
```

## Implementing factorial

To give you a simple example of how to program in `MIG`, let's implement
factorial. We won't do any model checking of this program; this is
merely to give you (the reader) a concrete sense of how programs can be
written in it.

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

into a `MIG` program. The program has three variables:

``` {.haskell .literate}
data FactVar = N | I | Res deriving (Show, Eq, Ord)
```

Now we're ready to write the `fact` program (line numbers are listed in
comments to the left of each statement):

``` {.haskell .literate}
fact :: Prog FactVar Int
fact = Vec.fromList
  {- 0 -} [ Modify (Res .= 1 >: I .= 2)
  {- 1 -} , IfGoto (pnot (var I .<= var N)) 5
  {- 2 -} ,   Modify (Res .= var Res * var I)
  {- 3 -} ,   Modify (I   .= var I   +     1)
  {- 4 -} ,   goto 1
  {- 5 -} , goto 5 -- halt
          ]
```

We don't have a separate `Halt` statement, so we model that with a
`goto` statement that points to itself, infinitely looping.

# Parallel programs

In this section, we will examine the problem of model checking multiple
programs running in parallel, which all have access to the same global
variable environment. We will use `MIG` to express each individual
program, and then we will define a function to convert a parallel
program into a transition system.

A *parallel program* is just a `Vector` of sequential programs with a
shared environment:

``` {.haskell .literate}
type ParProg var val = Vector (Prog var val)
```

We will use the term *process* to denote a sequential program that is
part of a larger parallel program. The *process id* of a particular
process is just the corresponding index into this vector.

``` {.haskell .literate}
type ProcId = Int
```

To "run" a parallel program, we first start each process at line 0.
Then, we arbitrarily pick which process will execute next, and we
execute that process's current statement, updating the global variable
environment and/or that process's current line number. This type of
parallel execution model is called *interleaving*, because each process
advances independently of the other, and the processes can advance in
any order.

## Example: Peterson's mutual exclusion algorithm

Consider two processes, P0 and P1, which are running corresponding
programs. Suppose that each program has a *critical section*, and if P0
and P1 are ever both in their critical sections, bad things can happen.
The property that both processes cannot execute their critical sections
simultaneously is called *mutual exclusion*.

Peterson's algorithm is an elegant way to ensure mutual exclusion. It
uses three variables: `Turn`, `Wait0`, and `Wait1`.

``` {.haskell .literate}
data PeteVar = Turn | Wait0 | Wait1 deriving (Show, Eq, Ord)
```

Intuitively, the meaning of each variable is as follows:

-   `Turn` is `False` it if is `P0`'s turn to enter its critical
    section, and `True` if it is `P1`'s turn.
-   `Wait0` is `True` if `P0` wishes to enter its critical section or is
    currently in its critical section, and `False` otherwise.
-   `Wait1` is `True` if `P1` wishes to enter its critical section or is
    currently in its critical section, and `False` otherwise.

We implement Peterson's algorithm in `MIG` as a parallel program with
two processes. Each process is in an infinite loop, continually
attempting to enter its own critical section. When a process wants to
enter its critical section, it first sets its own `Wait` variable to
`True`, and then it (somewhat counterintuitively) signals that it is the
*other* process's turn. Then, before it enters its own critical section,
it busy-waits until either the other process is not waiting, or its own
turn has arrived. Finally, when the critical section is complete, the
process sets its `Wait` variable to `False`, indicating it has exited
its critical section, and the other process is free to enter theirs. The
process then loops back to the beginning, and again attempts to enter
its critical section.

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

In order to model check a parallel program, we first convert such a
program into a transition system. The basic idea for the conversion will
be that a state in the transition system will be a pair
`(Vector LineNumber, Env var val)`, consisting of the current line
number of each process, and the current values of the global variable
environment.

Every state `(lineNums, env)` will have exactly `Vec.length lineNums`
outgoing transitions, each corresponding to executing the current line
of one of the running processes.

``` {.haskell .literate}
type ParProgState var val = (Vector LineNumber, Env var val)
```

What should the set of atomic propositional variables be for the
transition system of a program? Instead of choosing this for all
programs, we defer this choice to the caller. The caller will provide a
list of atomic propositional variables, along with a function which maps
each variable to a *state predicate*, i.e. a
`Predicate (ParProgState var val)`. Then, the label of each state will
be the set of variables whose corresponding predicate is true about the
current state.

The `action` type will just be a `(ProcId, LineNumber)` pair,
corresponding to "performing the statement at the given line of the
given process." As in the previous post, the `action` is just a name for
each transition, and does not have any semantic content whatsoever.

Let's define `parProgToTS`, which converts a parallel program to a
transition system:

``` {.haskell .literate}
parProgToTS :: [Env var val]
            -> [ap]
            -> (ap -> Predicate (ParProgState var val))
            -> ParProg var val
            -> TransitionSystem (ParProgState var val) (ProcId, LineNumber) ap
parProgToTS initialEnvs aps apToPred parProg = TransitionSystem
```

The `initialEnvs` argument is a list of all initial environments we are
considering. `aps` is the complete list of atomic propositional
variables, and `apToPred` maps each atomic propositional variable to its
corresponding state predicate. For each initial environment provided by
the caller, there is a corresponding initial state in the transition
system with every process starting at line 0:

``` {.haskell .literate}
  { tsInitialStates = [(Vec.replicate (Vec.length parProg) 0, env) | env <- initialEnvs]
```

States are labeled by the atomic propositional variables whose
corresponding predicates they satisfy:

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
              action = (procId, lineNum)
          in case process Vec.! lineNum of
            Modify effect ->
              (action, (lineNums Vec.// [(procId, lineNum+1)], effect env))
            IfGoto p lineNum'
              | env |= p  -> (action, (lineNums Vec.// [(procId, lineNum' )], env))
              | otherwise -> (action, (lineNums Vec.// [(procId, lineNum+1)], env))
```

## Checking Peterson's algorithm

The correctness property for Peterson's algorithm is simple: both
processes should never be in their critical sections simultaneously. To
ensure that this is true, we use the following type for the atomic
propositional variables:

``` {.haskell .literate}
data ProcAtLine = ProcAtLine ProcId LineNumber
  deriving (Show, Eq, Ord)
```

`ProcAtLine procId lineNum` represents the predicate that "process
`procId` is currently at line `lineNum`." This is codified by the
following function:

``` {.haskell .literate}
procAtLinePred :: ProcAtLine -> Predicate (ParProgState var val)
procAtLinePred (ProcAtLine procId lineNum) =
  \(lineNums, _) -> lineNums Vec.! procId == lineNum
```

In order to call `peteTS`, we also need to collect all of the atomic
propositional variables. These will be `ProcAtLine procId lineNum` for
every valid `(ProcId, LineNumber)` pair. We can collect all such pairs
for an arbitrary `ParProg` with the following function:

``` {.haskell .literate}
enumProcAtLine :: ParProg var val -> [ProcAtLine]
enumProcAtLine parProg =
  [ ProcAtLine procId lineNum | procId  <- [0..Vec.length parProg - 1]
                              , lineNum <- [0..Vec.length (parProg Vec.! procId) - 1] ]
```

Now, we can define the transition system for the `pete` program as
follows:

``` {.haskell .literate}
peteTS :: TransitionSystem (ParProgState PeteVar Bool) (ProcId, LineNumber) ProcAtLine
peteTS = parProgToTS [initialEnv] (enumProcAtLine pete) procAtLinePred pete
  where initialEnv = Map.fromList [ (Turn, False), (Wait0, False), (Wait1, False) ]
```

Note that there is only one initial environment; all three variables are
initially `False`.

The critical section occurs at line 3 in both processes, so the property
that both processes are not simultaneously in their critical sections is
stated as follows:

``` {.haskell}
pnot (atom (ProcAtLine 0 3) .& atom (ProcAtLine 1 3))
```

Let's check that this property is an invariant for `peteTS` transition
system:

``` {.haskell}
  > checkInvariant (pnot (atom (ProcAtLine 0 3) .& atom (ProcAtLine 1 3))) peteTS
  Nothing
```

Glancing back at each process in Peterson's algorithm, we see that the
assignment to the `Wait` variable occurs *before* the assignment to
`Turn`. What happens if we swap the two? Will our property still hold?

``` {.haskell .literate}
bad_pete_0 :: Prog PeteVar Bool
bad_pete_0 = Vec.fromList
  {- 0 -} [ Modify (Turn .= val True)
  {- 1 -} , Modify (Wait0 .= val True)
  {- 2 -} , IfGoto (var Turn .& var Wait1) 2
  {- 3 -} , noop -- CRITICAL SECTION
  {- 4 -} , Modify (Wait0 .= val False)
  {- 5 -} , goto 0
          ]
```

``` {.haskell .literate}
bad_pete_1 :: Prog PeteVar Bool
bad_pete_1 = Vec.fromList
  {- 0 -} [ Modify (Turn .= val False)
  {- 1 -} , Modify (Wait1 .= val True)
  {- 2 -} , IfGoto (pnot (var Turn) .& var Wait0) 2
  {- 3 -} , noop -- CRITICAL SECTION
  {- 4 -} , Modify (Wait1 .= val False)
  {- 5 -} , goto 0
          ]
```

``` {.haskell .literate}
bad_pete :: ParProg PeteVar Bool
bad_pete = Vec.fromList [ bad_pete_0, bad_pete_1 ]
```

``` {.haskell .literate}
bad_peteTS :: TransitionSystem (ParProgState PeteVar Bool) (ProcId, LineNumber) ProcAtLine
bad_peteTS = parProgToTS [initialEnv] (enumProcAtLine bad_pete) procAtLinePred bad_pete
  where initialEnv = Map.fromList [ (Turn, False), (Wait0, False), (Wait1, False) ]
```

The naming of these programs probably tips you off about the outcome of
our little experiment. Let's try it:

``` {.haskell}
  > checkInvariant (pnot (atom (ProcAtLine 0 3) .& atom (ProcAtLine 1 3))) bad_peteTS
  Just (([3,3],fromList [(Turn,True),(Wait0,True),(Wait1,True)]),Path {pathHead = ([0,0],fromList [(Turn,False),(Wait0,False),(Wait1,False)]), pathTail = [((0,0),([1,0],fromList [(Turn,True),(Wait0,False),(Wait1,False)])),((0,1),([2,0],fromList [(Turn,True),(Wait0,True),(Wait1,False)])),((0,2),([3,0],fromList [(Turn,True),(Wait0,True),(Wait1,False)])),((0,3),([4,0],fromList [(Turn,True),(Wait0,True),(Wait1,False)])),((0,4),([5,0],fromList [(Turn,True),(Wait0,False),(Wait1,False)])),((0,5),([0,0],fromList [(Turn,True),(Wait0,False),(Wait1,False)])),((1,0),([0,1],fromList [(Turn,False),(Wait0,False),(Wait1,False)])),((0,0),([1,1],fromList [(Turn,True),(Wait0,False),(Wait1,False)])),((0,1),([2,1],fromList [(Turn,True),(Wait0,True),(Wait1,False)])),((0,2),([3,1],fromList [(Turn,True),(Wait0,True),(Wait1,False)])),((1,1),([3,2],fromList [(Turn,True),(Wait0,True),(Wait1,True)])),((1,2),([3,3],fromList [(Turn,True),(Wait0,True),(Wait1,True)]))]})
```

Oh no! Looks like it doesn't hold. Let's make the counterexample a bit
more readable so we can analyze what went wrong:

``` {.haskell}
  > Just (_, path) = checkInvariant (pnot (atom (ProcAtLine 0 3) .& atom (ProcAtLine 1 3))) bad_peteTS
  > print (pathHead path) >> mapM_ print (snd <$> pathTail path)
  ([0,0],fromList [(Turn,False),(Wait0,False),(Wait1,False)])
  ([1,0],fromList [(Turn,True),(Wait0,False),(Wait1,False)])
  ([2,0],fromList [(Turn,True),(Wait0,True),(Wait1,False)])
  ([3,0],fromList [(Turn,True),(Wait0,True),(Wait1,False)])
  ([4,0],fromList [(Turn,True),(Wait0,True),(Wait1,False)])
  ([5,0],fromList [(Turn,True),(Wait0,False),(Wait1,False)])
  ([0,0],fromList [(Turn,True),(Wait0,False),(Wait1,False)])
  ([0,1],fromList [(Turn,False),(Wait0,False),(Wait1,False)])
  ([1,1],fromList [(Turn,True),(Wait0,False),(Wait1,False)])
  ([2,1],fromList [(Turn,True),(Wait0,True),(Wait1,False)])
  ([3,1],fromList [(Turn,True),(Wait0,True),(Wait1,False)])
  ([3,2],fromList [(Turn,True),(Wait0,True),(Wait1,True)])
  ([3,3],fromList [(Turn,True),(Wait0,True),(Wait1,True)])
```

Here is the important bit, annotated with letters for discussion:

``` {.haskell}
  ([0,0],fromList [(Turn,True),(Wait0,False),(Wait1,False)])  -- a
  ([0,1],fromList [(Turn,False),(Wait0,False),(Wait1,False)]) -- b
  ([1,1],fromList [(Turn,True),(Wait0,False),(Wait1,False)])  -- c
  ([2,1],fromList [(Turn,True),(Wait0,True),(Wait1,False)])   -- d
  ([3,1],fromList [(Turn,True),(Wait0,True),(Wait1,False)])   -- e
  ([3,2],fromList [(Turn,True),(Wait0,True),(Wait1,True)])    -- f
  ([3,3],fromList [(Turn,True),(Wait0,True),(Wait1,True)])    -- g
```

At a, both processes are at line 0. First, P1 sets `Turn` to `False`,
indicating it is P0's turn to enter the critical section. Then, P0 sets
it to `True`, indicating it is P1's turn. Then, at c, P0 sets `Wait0` to
`True`, indicating it wishes to enter. At line d, P0 enters its critical
section even though `Turn` is `True`, because `Wait1` is still `False`.
Then, P1 is able to enter *its* critical section, because `Turn` is
`True`.

We see that it *really matters* that the `Wait` variables are updated
*before* the `Turn` flag is flipped! Otherwise, the algorithm simply
does not work.

## What's next?

In this post, we applied model checking to a real-world program and
proved something valuable and non-trivial. Peterson's algorithm isn't
*too* complicated, but it's not straightforward to see why it's correct
at first glance. We saw that by translating it to a transition system,
we could exhaustively explore the reachable state space, and found that
it was impossible to violate the desired invariant. When we modified the
program slightly, we discovered that the invariant failed. Furthermore,
the model checking approach discovered a counterexample that helped us
to understand *why* it failed.

So far in this series, the only properties we have explored and checked
are *invariants*. However, there are some properties that cannot be
expressed as invariants; for instance, the property that a traffic light
will be green infinitely often, or that a yellow light always precedes a
red light. In the next post, we will explore a larger class of
properties called *regular safety properties*. We will show how to use
*nondeterministic finite automata* to express such properties, and how
to check whether these properties hold.
