## `NTAC` {#Tactic.NTAC}


```
NTAC : int -> tactic -> tactic
```



Apply tactic a specified number of times.


An invocation `NTAC n tac` applies the tactic `tac`
exactly `n` times. If `n <= 0` then the goal is unchanged.

### Failure

Fails if `tac` fails.

### Example

Suppose we have the following goal:
    
      ?- x = y
    
We apply a tactic for symmetry of equality 3 times:
    
      NTAC 3 (PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ])
    
and obtain
    
      ?- y = x
    


Controlling iterated application tactics.



### See also

[`Rewrite.PURE_ONCE_REWRITE_TAC`](#Rewrite.PURE_ONCE_REWRITE_TAC), [`Tactical.REPEAT`](#Tactical.REPEAT), [`Conv.REPEATC`](#Conv.REPEATC)

