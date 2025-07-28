## `CHECK_ASSUME_TAC` {#Tactic.CHECK_ASSUME_TAC}


```
CHECK_ASSUME_TAC : thm_tactic
```



Adds a theorem to the assumption list of goal, unless it solves the goal.


When applied to a theorem `A' |- s` and a goal `A ?- t`, the tactic
`CHECK_ASSUME_TAC` checks whether the theorem will solve the goal (this
includes the possibility that the theorem is just `A' |- F`). If so, the goal
is duly solved. If not, the theorem is added to the assumptions of the goal,
unless it is already there.
    
           A ?- t
       ==============  CHECK_ASSUME_TAC (A' |- F)   [special case 1]
    
    
           A ?- t
       ==============  CHECK_ASSUME_TAC (A' |- t)   [special case 2]
    
    
           A ?- t
       ==============  CHECK_ASSUME_TAC (A' |- s)   [general case]
        A u {s} ?- t
    
Unless `A'` is a subset of `A`, the tactic will be invalid, although
it will not fail.

### Failure

Never fails.

### See also

[`Tactic.ACCEPT_TAC`](#Tactic.ACCEPT_TAC), [`Tactic.ASSUME_TAC`](#Tactic.ASSUME_TAC), [`Tactic.CONTR_TAC`](#Tactic.CONTR_TAC), [`Tactic.DISCARD_TAC`](#Tactic.DISCARD_TAC), [`Tactic.MATCH_ACCEPT_TAC`](#Tactic.MATCH_ACCEPT_TAC)

