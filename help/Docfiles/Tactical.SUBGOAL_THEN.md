## `SUBGOAL_THEN` {#Tactical.SUBGOAL_THEN}


```
SUBGOAL_THEN : term -> thm_tactic -> tactic
```



Allows the user to introduce a lemma.


The user proposes a lemma and is then invited to prove it under the
current assumptions.  The lemma is then used with the `thm_tactic` to
simplify the goal.  That is, if
    
        A1 ?- t1
       ==========  f (u |- u)
        A2 ?- t2
    
then
    
             A1 ?- t1
       ====================  SUBGOAL_THEN u f
        A1 ?- u   A2 ?- t2
    

Typically `f (u |- u)` will be an invalid tactic because it would
return a validation function which generated the theorem `A1,u |- t1`
from the theorem `A2 |- t2`.  Nonetheless, the tactic
`SUBGOAL_THEN u f` is valid because of the extra sub-goal where `u`
must be proved.

### Failure

`SUBGOAL_THEN` will fail if an attempt is made to use a
nonboolean term as a lemma.


When combined with `rotate`, `SUBGOAL_THEN` allows the user to defer
some part of a proof and to continue with another part.
`SUBGOAL_THEN` is most convenient when the tactic solves the original
goal, leaving only the subgoal.  For example, suppose the user wishes
to prove the goal
    
       {n = SUC m} ?- (0 = n) ==> t
    
Using `SUBGOAL_THEN` to focus on the case in which `~(n = 0)`,
rewriting establishes it truth, leaving only the proof that `~(n = 0)`.
That is,
    
       SUBGOAL_THEN (Term `~(0 = n)`) (fn th => REWRITE_TAC [th])
    
generates the following subgoals:
    
       {n = SUC m} ?-  ~(0 = n)
       ?- T
    

### Comments

Some users may expect the generated tactic to be `f (A1 |- u)`, rather
than `f (u |- u)`.
