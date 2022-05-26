
Example: A program with a data race
--

Consider the following C program:

```c
int counter = 0;

void incr() {
  int tmp = counter;
  counter = tmp + 1;
}
```

This program has a single global variable, `counter`. The function `incr`
increments the counter. Note that the process of *reading* the current value of
the counter and *writing* the modified value are separate steps in the program.
If we spawn two separate threads, each of which runs incr(), we might expect
that after the execution of the program, the value of `counter` will be 2.
However, this assumption is false, because after the value of `counter` is read
by the first thread, it might also be read by the second thread before the first
thread has incremented it. In this case, both threads end up writing the same
value to the counter.

Let's convert this program into a parallel program in our language, with two
separate processes, each running its own instance of `incr`. Since the variable
`tmp` is not actually shared between the two processes, we'll be sure to use
different names for these variables in each process.

> data IncrVar = Counter | Tmp1 | Tmp2 deriving (Show, Eq, Ord)

> incrProc :: IncrVar -> Prog IncrVar Int
> incrProc tmp = Vec.fromList
>   {- 0 -} [ Modify (tmp .= var Counter)
>   {- 1 -} , Modify (Counter .= var tmp .+ val 1)
>   {- 2 -} , goto 2
>           ]

> dataRace :: ParProg IncrVar Int
> dataRace = Vec.fromList [ incrProc Tmp1
>                         , incrProc Tmp2 ]

In the next section, we will discuss out to convert a program like this into a
transition system.

Converting the data race program to a transition system
--

As for sequential programs, before converting the data race program to a
transition system, we first must decide what the initial environments are, what
the atomic propositional variables are, and how those variables map to state
predicates. For the data race program, we will only have one initial
environment, with all variables initially `0`. The only atomic propositions we
will consider will be ones that indicate whether a particular process is at a
particular line:

> data DataRaceProp = DataRaceProcAtLine ProcId LineNumber
>   deriving (Show, Eq, Ord)

> dataRaceProps :: [DataRaceProp]
> dataRaceProps = [ DataRaceProcAtLine procId lineNum | procId <- [0..1], lineNum <- [0..1] ]

> dataRacePropPred :: DataRaceProp -> Predicate (Vector LineNumber, Env IncrVar Int)
> dataRacePropPred (DataRaceProcAtLine procId lineNum) = procAtLine procId lineNum

Now, we define `dataRaceTS` in terms of the above:

> dataRaceTS :: TransitionSystem (Vector LineNumber, Env IncrVar Int) (ProcId, LineNumber) DataRaceProp
> dataRaceTS = parProgToTS [initialEnv] dataRaceProps dataRacePropPred dataRace
>   where initialEnv = Map.fromList [(Counter, 0), (Tmp1, 0), (Tmp2, 0)]

![Transition system for the `dataRace` program](../images/data_race.png){width=100% height=100%}

Model checking Peterson's algorithm
--

Conclusion
==

Converting the factorial program to a transition system
--

In converting a program to a transition system, we first need to choose:

1) The set of all possible initial environments
2) The set of all atomic propositional variables
3) How each atomic propositional variable maps to a *predicate* about the
   current line number and environment

In fact, these are the first three arguments of the `progToTS` function. The
choices we make will depend on what kinds of properties we want to verify, and
what the set of possible starting states we will want to consider.

For our factorial program, the property we'll be interested in checking is a
loop invariant which will hold at the beginning of the loop. Whenever the
program is at line 1, the following formula should hold:

```
Res == factorial(I-1)
```

In other words, the current value of `Res` should be the "product so far." We'd
also like to check this loop invariant for not just one particular input value
of `n`, but for a range of inputs.

In light of these considerations, we'll making the following respective choices:

1) The set of possible initial environments will be the set of all environments
   with `N = i` for all `i` between `1` and some maximum integer `n`. (We'll
   initialize `Res` and `I` to `0` for completeness, but we note that their
   initial values don't matter, since the first line of the program sets their
   values.)

2) We will have two types of atomic propositional variables: ones that indicate
   whether the current line number is a particular value, and a single
   proposition that indicates whether the condition `Res == factorial(I-1)` is
   true.

3) We will map the variables described in 2) to the corresponding predicates
   about the current `(LineNumber, Env var val)` state in the transition system.

Our atomic propositions will be of the following type:

> data FactProp = FactAtLine Int
>               | FactResInvariant
>   deriving (Show, Eq, Ord)

The full set of propositions is `FactResInvariant`, plus `FactAtLine i` for
every line `i` of the `fact` program:

> factProps :: [FactProp]
> factProps = FactResInvariant : [ FactAtLine i | i <- [0..Vec.length fact-1] ]

We use the following mapping from `FactProp` to state predicates:

> factPropPred :: FactProp -> Predicate (LineNumber, Env FactVar Int)
> factPropPred (FactAtLine i) = atLine i
> factPropPred FactResInvariant =
>   atEnv $ var Res .== liftFun factorial (var I .- val 1)
>   where factorial n = product [1..n]

Now, we define `factTS` in terms of the above:

> factTS :: Int -> TransitionSystem (LineNumber, Env FactVar Int) LineNumber FactProp
> factTS n = progToTS initialEnvs factProps factPropPred fact
>   where initialEnvs = [ Map.fromList [(N, i), (Res, 0), (I, 0)] | i <- [1..n] ]

Let's check our loop invariant for `factTS` for all values of `n` from `1` to
`20`. First, let's see if `FactResInvariant` holds unconditionally:

```haskell
  > checkInvariant (atom FactResInvariant) (factTS 20)
  Just ((0,fromList [(N,1),(I,0),(Res,0)]),Path {pathHead = (0,fromList [(N,1),(I,0),(Res,0)]), pathTail = []})
```

The invariant trivially fails at line 0, because `I` and `Res` haven't been
initialized yet. Let's see if we can fix this by assuming we are not at line 0.

```haskell
  > checkInvariant (pnot (atom (FactAtLine 0)) .-> atom FactResInvariant) (factTS 20)
  Just ((3,fromList [(N,2),(I,2),(Res,2)]),Path {pathHead = (0,fromList [(N,2),(I,0),(Res,0)]), pathTail = [(0,(1,fromList [(N,2),(I,2),(Res,1)])),(1,(2,fromList [(N,2),(I,2),(Res,1)])),(2,(3,fromList [(N,2),(I,2),(Res,2)]))]})
```

The invariant fails at line 3, because `Res` has been updated, but `I` has not
been incremented. What we *really* care about is that the invariant holds at the
beginning every loop iteration, which is at line 1. So let's just check that
whenever we are at line 1, the invariant holds.

```haskell
  > checkInvariant (atom (FactAtLine 1) .-> atom FactResInvariant) (factTS 20)
  Nothing
```

A note on sequential programs
--

The language we have defined in this post is entirely *deterministic*; that is,
for every state in the transition system derived from any program, there is
exactly one outgoing transition. This means that the process of building a
transition system is equivalent to *simulating* the program in question.

We can see this easily by looking at a picture of `factTS 4`. Each state's name
is written in the format `lineNum: <n=value, res=value>`:

![Transition system for the `fact` function with inputs `n = 1` through `4`](../images/fact.png){width=100% height=100%}

We can plainly see that the graph is just a collection of linear sequences of
states. There is one sequence for every distinct initial environment we passed
to the conversion function.

This illustrates a basic limitation of *explicit state* model checking: one
cannot prove that a property holds for *arbitrary* program inputs, unless the
input space is finite and it is feasible to try every single input. In *symbolic
state* model checking, one represents the states symbolically, which allows one
to prove properties about all inputs, under certain conditions; however, that
falls outside the scope of this series.

From sequential programs to transition systems
==

In order to model check programs, we'll need to be able to convert a program
into a transition system. The basic idea will be that a state in the transition
system will be a pair `(LineNumber, Env var val)`, consisting of the current
line number and the current values of the program variables. Each state will
have exactly one outgoing transition, which corresponds to executing the
statement at the current line of the program and then going to the next line to
be executed.

The atomic propositional variables will be defined by the caller. The caller
will provide a list of variables, along with a function mapping each variable to
some predicate involving the current line number and global variable
environment. Then, the label of each state will be the set of variables whose
corresponding predicate is true at the current `(LineNumber, Env var val)` pair.

The `action` type will just be `LineNumber`, corresponding to "performing the
statement at the given line." As before, the `action` is just a name for each
transition, and does not have any semantic content whatsoever.

> progToTS :: [Env var val]
>          -> [ap]
>          -> (ap -> Predicate (LineNumber, Env var val))
>          -> Prog var val
>          -> TransitionSystem (LineNumber, Env var val) LineNumber ap
> progToTS initialEnvs aps apToPred prog = TransitionSystem

The first argument to this function, `initialEnvs`, is a list of possible
initial environments for the program. Every program starts at line `0`. For each
initial environment provided by the caller, there is a corresponding initial
state in the transition system that starts the program at line `0` with that
initial environment:

>   { tsInitialStates = [ (0, env) | env <- initialEnvs ]

Given a state `s :: (LineNumber, Env var val)`, the label of `s` is the set of
all atomic propositional variables (as supplied by the caller) whose
corresponding environment predicate is satisified by `s`:

>   , tsLabel = \s -> [ p | p <- aps, s |= apToPred p ]

Each state `(lineNum, env) :: (LineNumber, Env var val)` has a single outgoing
transition. To determine what the transition should be, we first look up the
statement at the current line number:

>   , tsTransitions = \(lineNum, env) -> case prog Vec.! lineNum of

The `Modify` statement transitions to the next line, and modifies the
environment by applying the given effect:

>       Modify effect -> [(lineNum, (lineNum+1, effect env))]

The `IfGoto` statement tests the environment predicate; if it's true, we
transition to the given line number, and if it's false, we transition to the
next line number. In both cases, the global variable environment is left
unchanged.

>       IfGoto p lineNum'
>         | env |= p  -> [(lineNum, (lineNum' , env))]
>         | otherwise -> [(lineNum, (lineNum+1, env))]
>   }

Atomic propositions
--

When translating a program to a transition system, we need to define our set of
atomic propositional variables, which amounts to identifying a few predicates
about our state which we are interested in. We also need to map each variable to
its corresponding predicate when we call `progToTS`. This map needs to be a
function of type `ap -> Predicate (LineNumber, Env var val)`; that is, our
atomic propositions will denote predicates that take the current line number
into account as well as the global variable environment.

The following "lifting" operators will be nice to have, as they will enable us
to smoothly define such predicates:

> liftL :: Predicate a -> Predicate (a, b)
> liftL p (a, _) = p a

> liftR :: Predicate b -> Predicate (a, b)
> liftR p (_, b) = p b

With these operators, we can lift a predicate about an `Env var val` to a
predicate about a `(LineNumber, Env var val)` pair:

> atEnv :: Predicate (Env var val) -> Predicate (a, Env var val)
> atEnv = liftR

Furthermore, we sometimes will wish to define invariants that only apply when we
are at a specific line number, so the following function will be useful:

> atLine :: LineNumber -> Predicate (LineNumber, a)
> atLine lineNum = liftL (== lineNum)
