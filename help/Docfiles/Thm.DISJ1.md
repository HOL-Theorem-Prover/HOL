## `DISJ1` {#Thm.DISJ1}


```
DISJ1 : thm -> term -> thm
```



Introduces a right disjunct into the conclusion of a theorem.


    
           A |- t1
       ---------------  DISJ1 (A |- t1) t2
        A |- t1 \/ t2
    



### Failure

Fails unless the term argument is boolean.

### Example

    
    - DISJ1 TRUTH F;
    > val it = |- T \/ F : thm
    



### See also

[`Tactic.DISJ1_TAC`](#Tactic.DISJ1_TAC), [`Thm.DISJ2`](#Thm.DISJ2), [`Tactic.DISJ2_TAC`](#Tactic.DISJ2_TAC), [`Thm.DISJ_CASES`](#Thm.DISJ_CASES)

