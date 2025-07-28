## `DISJ2_TAC` {#Tactic.DISJ2_TAC}


```
DISJ2_TAC : tactic
```



Selects the right disjunct of a disjunctive goal.


    
        A ?- t1 \/ t2
       ===============  DISJ2_TAC
           A ?- t2
    



### Failure

Fails if the goal is not a disjunction.

### See also

[`Thm.DISJ1`](#Thm.DISJ1), [`Tactic.DISJ1_TAC`](#Tactic.DISJ1_TAC), [`Thm.DISJ2`](#Thm.DISJ2)

