---
title: "Model Checking in Haskell, Part 2: From Programs to Transition
  Systems"
---

``` {.haskell .literate}
module ModelChecking2 where

import ModelChecking1 hiding ( TransitionSystem(..) )

import Data.List (find)
import Prelude hiding (not)

data TransitionSystem s a ap = TransitionSystem
  { tsInitials :: [s]
  , tsTransitions :: [(s, a, s)]
  , tsLabel :: s -> Assignment ap
  }

checkInvariant :: Eq s => Proposition ap -> TransitionSystem s a ap -> Maybe [s]
checkInvariant p ts =
  let rs = reachables (tsInitials ts) (omitLabel <$> tsTransitions ts)
  in path <$> find (\(s,_) -> tsLabel ts s |= not p) rs
  where omitLabel (s, a, s') = (s, s')
        path (s, rpath) = reverse (s:rpath)

data VarType = IntType | BoolType
```
