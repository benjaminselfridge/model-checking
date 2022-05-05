# Introduction to model checking (with Haskell!), Part 2

``` {.haskell .literate}
module ModelChecking2 where
```

We'll build on concepts in the previous lesson, so let's import that
now.

``` {.haskell .literate}
data NFA q ap = NFA
  { nfaTransitions :: [(q, Proposition ap, q)]
  , nfaInitials :: [q]
  , nfaFinals :: [q]
  }
```

``` {.haskell .literate}
nextStatesOn :: NFA q ap -> q -> Assignment ap -> [q]
nextStatesOn nfa q f = [ q' | (q, p, q') <- nfaTransitions nfa, f |= p ]
```

``` {.haskell .literate}
-- | Product of a transition system and an NFA.
(*) :: Eq q
    => TransitionSystem s ap
    -> NFA q ap
    -> TransitionSystem (s, q) q
ts * nfa = TransitionSystem
  { tsTransitions =
      [ ((s, q), (s', q')) | (s, s') <- tsTransitions ts
                           , (q, p, q') <- nfaTransitions nfa
                           , tsLabel ts s' |= p
                           ]
  , tsInitials =
      [ (s, q) | s  <- tsInitials ts
               , q0 <- nfaInitials nfa
               , q  <- nextStatesOn nfa q0 (tsLabel ts s)
               ]
  , tsLabel = \(s, q) -> only q
  }
```

``` {.haskell .literate}
data Color = Red | Yellow | Green
  deriving (Eq, Show)
```

``` {.haskell .literate}
traffic_light :: TransitionSystem Color Color
traffic_light = TransitionSystem
  { tsInitials = [Green]
  , tsTransitions = [ (Red, Green), (Green, Yellow)
                    , (Yellow, Red), (Green, Red) ]
  , tsLabel = \color -> only color
  }
```

``` {.haskell .literate}
yellow_before_red :: NFA Int Color
yellow_before_red = NFA
  { nfaInitials = [0]
  , nfaFinals = [1]
  , nfaTransitions = [ (0, atom Green, 0)
                     , (0, atom Yellow, 1)
                     , (0, atom Red, 2)
                     , (2, atom Yellow, 2)
                     , (2, not (atom Yellow), 0)
                     ]
  }
```
