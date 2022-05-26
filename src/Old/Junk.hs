
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
