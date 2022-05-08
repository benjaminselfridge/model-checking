Now...

> module ModelChecking3 where
>
> import ModelChecking1
> import ModelChecking2
>
> import Data.Map.Strict ((!), unionWithKey, insert, fromList)

Do a thing

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

If the lock is set, 

> data ProcessAction = StartWaiting | SetLock | UnsetLock
>   deriving (Eq, Show, Ord)

> data Lock = Lock deriving (Eq, Show, Ord)

Must be equal to. Put this in ModelChecking2.

> (=!=) :: (Ord var, Eq val) => var -> val -> Cond var val
> (var =!= val) state = state ! var == val

Set equal to. Read as "becomes". Put this in ModelChecking2.

> (=:=) :: Ord var => var -> val -> Effect var val
> (=:=) = insert

The trivial condition. Put this in ModelChecking2.

> unconditionally :: Cond var val
> unconditionally = const True

> process :: ProgramGraph ProcessLoc ProcessAction Lock Bool
> process = ProgramGraph
>   { pgTransitions = \loc -> case loc of
>       NonCrit -> [ ( unconditionally, StartWaiting, Wait    ) ]
>       Wait    -> [ ( Lock =!= False , SetLock     , Crit    ) ]
>       Crit    -> [ ( unconditionally, UnsetLock   , NonCrit ) ]
>   , pgEffect = \action -> case action of
>       StartWaiting -> id
>       SetLock      -> Lock =:= True
>       UnsetLock    -> Lock =:= False
>   , pgInitialLocations = [ NonCrit ]
>   , pgInitialState = fromList [ (Lock, False) ]
>   }
>
