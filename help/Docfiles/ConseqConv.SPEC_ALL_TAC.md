## `SPEC_ALL_TAC` {#ConseqConv.SPEC_ALL_TAC}


```
SPEC_ALL_TAC : tactic
```



Generalizes a goal.


When applied to a goal `A ?- t`, the tactic `SPEC_ALL_TAC` generalizes
all variables that are free in `t`, but not in `A`. This results in a
goal of the form `A ?- !x1 ... xn. t`.
    
               A ?- t
       ====================  SPEC_ALL_TAC
        A ?- !x1 ... xn. t
    

### Example

    
       - val _ = set_goal ([``(P x):bool``], ``Q x /\ Z y``)
       > Initial goal:
    
         Q x /\ Z y
         ------------------------------------
           P x
    
       - e(SPEC_ALL_TAC)
       >
         !Q Z y. Q x /\ Z y
         ------------------------------------
           P x
    

### Failure

`SPEC_ALL_TAC` never fails. However, maybe no variable is generalized.

### See also

[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC)

