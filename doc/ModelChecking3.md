---
title: "Model Checking in Haskell, Part 3: Parallelism"
---

-   [[1]{.toc-section-number} Interleaving](#interleaving)

Now...

``` {.haskell .literate}
module ModelChecking3 where
```

``` {.haskell .literate}
import ModelChecking1
import ModelChecking2
```

``` {.haskell .literate}
import Control.Arrow ((>>>))
import Data.Map.Strict ((!), unionWithKey, insert, fromList)
import Prelude hiding (not)
```

# Interleaving

``` {.haskell .literate}
(|||) :: (Ord var, Show var, Eq val)
      => ProgramGraph loc1 action1 var val
      -> ProgramGraph loc2 action2 var val
      -> ProgramGraph (loc1, loc2) (Either action1 action2) var val
pg1 ||| pg2 = ProgramGraph
  { pgTransitions = \(loc1, loc2) ->
      [ (guard, Left action,  (loc1', loc2)) | (guard, action, loc1') <- pgTransitions pg1 loc1 ] ++
      [ (guard, Right action, (loc1, loc2')) | (guard, action, loc2') <- pgTransitions pg2 loc2 ]
  , pgEffect = \eAction -> case eAction of
      Left  action -> pgEffect pg1 action
      Right action -> pgEffect pg2 action
  , pgInitialLocations = [(loc1, loc2) | loc1 <- pgInitialLocations pg1
                                       , loc2 <- pgInitialLocations pg2 ]
  , pgInitialState = unionWithKey mustBeEqual (pgInitialState pg1) (pgInitialState pg2)
  }
  where mustBeEqual k a b | a == b = a
                          | otherwise = error $ "program graphs disagree on variable " ++ show k
```

``` {.haskell .literate}
data ProcessLoc = NonCrit | Wait | Crit
  deriving (Eq, Show, Ord)
```

``` {.haskell .literate}
data ProcessAction = StartWaiting | EnterCrit | ExitCrit
  deriving (Eq, Show, Ord)
```

``` {.haskell .literate}
data Lock = Lock deriving (Eq, Show, Ord)
```

``` {.haskell .literate}
process :: ProgramGraph ProcessLoc ProcessAction Lock Bool
process = ProgramGraph
  { pgTransitions = \loc -> case loc of
      NonCrit -> [ ( unconditionally, StartWaiting, Wait    ) ]
      Wait    -> [ ( Lock !== False , EnterCrit   , Crit    ) ]
      Crit    -> [ ( unconditionally, ExitCrit    , NonCrit ) ]
  , pgEffect = \action -> case action of
      StartWaiting -> id
      EnterCrit    -> Lock =: True
      ExitCrit     -> Lock =: False
  , pgInitialLocations = [ NonCrit ]
  , pgInitialState = fromList [ (Lock, False) ]
  }
```

``` {.haskell .literate}
data PetersonVar = B1
                 | B2
                 | X
  deriving (Show, Eq, Ord)
```

``` {.haskell .literate}
peterson_process_1 :: ProgramGraph ProcessLoc ProcessAction PetersonVar Bool
peterson_process_1 = ProgramGraph
  { pgTransitions = \loc -> case loc of
      NonCrit -> [ ( unconditionally            , StartWaiting, Wait    ) ]
      Wait    -> [ ( X !== False .| B2 !== False, EnterCrit   , Crit    ) ]
      Crit    -> [ ( unconditionally            , ExitCrit    , NonCrit ) ]
  , pgEffect = \action -> case action of
      StartWaiting -> B1 =: True >>> X =: True
      EnterCrit    -> id
      ExitCrit     -> B1 =: False
  , pgInitialLocations = [ NonCrit ]
  , pgInitialState = fromList [ (B1, False), (B2, False), (X, False) ]
  }
```

``` {.haskell .literate}
peterson_process_2 :: ProgramGraph ProcessLoc ProcessAction PetersonVar Bool
peterson_process_2 = ProgramGraph
  { pgTransitions = \loc -> case loc of
      NonCrit -> [ ( unconditionally           , StartWaiting, Wait    ) ]
      Wait    -> [ ( X !== True .| B1 !== False, EnterCrit   , Crit    ) ]
      Crit    -> [ ( unconditionally           , ExitCrit    , NonCrit ) ]
  , pgEffect = \action -> case action of
      StartWaiting -> B2 =: True >>> X =: False
      EnterCrit    -> id
      ExitCrit     -> B2 =: False
  , pgInitialLocations = [ NonCrit ]
  , pgInitialState = fromList [ (B1, False), (B2, False), (X, False) ]
  }
```

``` {.haskell .literate}
peterson :: ProgramGraph (ProcessLoc, ProcessLoc) (Either ProcessAction ProcessAction) PetersonVar Bool
peterson = peterson_process_1 ||| peterson_process_2

handshake :: TransitionSystem s1 action ap
          -> TransitionSystem s1 action ap
          -> TransitionSystem (s1, s2) action ap
handshake ts1 ts2 = undefined
```
