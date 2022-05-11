Now...

> module ModelChecking3 where

> import ModelChecking1
> import ModelChecking2

> import Control.Arrow ((>>>))
> import Data.Map.Strict ((!), unionWithKey, insert, fromList)
> import Prelude hiding (not)

Interleaving
============

> (|||) :: (Ord var, Show var, Eq val)
>       => ProgramGraph loc1 action1 var val
>       -> ProgramGraph loc2 action2 var val
>       -> ProgramGraph (loc1, loc2) (Either action1 action2) var val
> pg1 ||| pg2 = ProgramGraph
>   { pgTransitions = \(loc1, loc2) ->
>       [ (guard, Left action,  (loc1', loc2)) | (guard, action, loc1') <- pgTransitions pg1 loc1 ] ++
>       [ (guard, Right action, (loc1, loc2')) | (guard, action, loc2') <- pgTransitions pg2 loc2 ]
>   , pgEffect = \eAction -> case eAction of
>       Left  action -> pgEffect pg1 action
>       Right action -> pgEffect pg2 action
>   , pgInitialLocations = [(loc1, loc2) | loc1 <- pgInitialLocations pg1
>                                        , loc2 <- pgInitialLocations pg2 ]
>   , pgInitialState = unionWithKey mustBeEqual (pgInitialState pg1) (pgInitialState pg2)
>   }
>   where mustBeEqual k a b | a == b = a
>                           | otherwise = error $ "program graphs disagree on variable " ++ show k

> data ProcessLoc = NonCrit | Wait | Crit
>   deriving (Eq, Show, Ord)

> data ProcessAction = StartWaiting | EnterCrit | ExitCrit
>   deriving (Eq, Show, Ord)

> data Lock = Lock deriving (Eq, Show, Ord)

> process :: ProgramGraph ProcessLoc ProcessAction Lock Bool
> process = ProgramGraph
>   { pgTransitions = \loc -> case loc of
>       NonCrit -> [ ( unconditionally, StartWaiting, Wait    ) ]
>       Wait    -> [ ( Lock !== False , EnterCrit   , Crit    ) ]
>       Crit    -> [ ( unconditionally, ExitCrit    , NonCrit ) ]
>   , pgEffect = \action -> case action of
>       StartWaiting -> id
>       EnterCrit    -> Lock =: True
>       ExitCrit     -> Lock =: False
>   , pgInitialLocations = [ NonCrit ]
>   , pgInitialState = fromList [ (Lock, False) ]
>   }

> data PetersonVar = B1
>                  | B2
>                  | X
>   deriving (Show, Eq, Ord)

> peterson_process_1 :: ProgramGraph ProcessLoc ProcessAction PetersonVar Bool
> peterson_process_1 = ProgramGraph
>   { pgTransitions = \loc -> case loc of
>       NonCrit -> [ ( unconditionally            , StartWaiting, Wait    ) ]
>       Wait    -> [ ( X !== False .| B2 !== False, EnterCrit   , Crit    ) ]
>       Crit    -> [ ( unconditionally            , ExitCrit    , NonCrit ) ]
>   , pgEffect = \action -> case action of
>       StartWaiting -> B1 =: True >>> X =: True
>       EnterCrit    -> id
>       ExitCrit     -> B1 =: False
>   , pgInitialLocations = [ NonCrit ]
>   , pgInitialState = fromList [ (B1, False), (B2, False), (X, False) ]
>   }

> peterson_process_2 :: ProgramGraph ProcessLoc ProcessAction PetersonVar Bool
> peterson_process_2 = ProgramGraph
>   { pgTransitions = \loc -> case loc of
>       NonCrit -> [ ( unconditionally           , StartWaiting, Wait    ) ]
>       Wait    -> [ ( X !== True .| B1 !== False, EnterCrit   , Crit    ) ]
>       Crit    -> [ ( unconditionally           , ExitCrit    , NonCrit ) ]
>   , pgEffect = \action -> case action of
>       StartWaiting -> B2 =: True >>> X =: False
>       EnterCrit    -> id
>       ExitCrit     -> B2 =: False
>   , pgInitialLocations = [ NonCrit ]
>   , pgInitialState = fromList [ (B1, False), (B2, False), (X, False) ]
>   }

> peterson :: ProgramGraph (ProcessLoc, ProcessLoc) (Either ProcessAction ProcessAction) PetersonVar Bool
> peterson = peterson_process_1 ||| peterson_process_2
>
> handshake :: Eq action
>           => [action]
>           -> TransitionSystem s1 action ap1
>           -> TransitionSystem s2 action ap2
>           -> TransitionSystem (s1, s2) action (Either ap1 ap2)
> handshake h ts1 ts2 = TransitionSystem
>   { tsInitialStates = [ (s1, s2) | s1 <- tsInitialStates ts1
>                                  , s2 <- tsInitialStates ts2 ]
>   , tsLabel = \(s1, s2) p -> case p of
>       Left  p1 -> tsLabel ts1 s1 p1
>       Right p2 -> tsLabel ts2 s2 p2
>   , tsTransitions = \(s1, s2) ->
>       [ (action, (s1', s2))  | (action, s1') <- tsTransitions ts1 s1
>                              , action `notElem` h ] ++
>       [ (action, (s1, s2'))  | (action, s2') <- tsTransitions ts2 s2
>                              , action `notElem` h ] ++
>       [ (action, (s1', s2')) | (action , s1') <- tsTransitions ts1 s1
>                              , (action', s2') <- tsTransitions ts2 s2
>                              , action == action' ]
>   }
>
> data BookingEvent = Scan | Store | PrintCmd | Print
>   deriving (Show, Eq, Ord)
>
> bar_code_reader :: TransitionSystem Int BookingEvent Int
> bar_code_reader = TransitionSystem
>   { tsInitialStates = [0]
>   , tsLabel = (==)
>   , tsTransitions = \s -> case s of
>       0 -> [(Scan , 1)]
>       1 -> [(Store, 0)]
>   }
>
> booking_program :: TransitionSystem Int BookingEvent Int
> booking_program = TransitionSystem
>   { tsInitialStates = [0]
>   , tsLabel = (==)
>   , tsTransitions = \s -> case s of
>       0 -> [(Store, 1)]
>       1 -> [(PrintCmd, 0)]
>   }
>
> printer :: TransitionSystem Int BookingEvent Int
> printer = TransitionSystem
>   { tsInitialStates = [0]
>   , tsLabel = (==)
>   , tsTransitions = \s -> case s of
>       0 -> [(PrintCmd, 1)]
>       1 -> [(Print, 0)]
>   }
>
> booking = handshake [Print]
>   (handshake [Store] bar_code_reader booking_program)
>   printer
