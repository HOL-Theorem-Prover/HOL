## `CONTR_TAC` {#Tactic.CONTR_TAC}


```
CONTR_TAC : thm_tactic
```



Solves any goal from contradictory theorem.


When applied to a contradictory theorem `A' |- F`, and a goal `A ?- t`,
the tactic `CONTR_TAC` completely solves the goal. This is an invalid
tactic unless `A'` is a subset of `A`.
    
        A ?- t
       ========  CONTR_TAC (A' |- F)
    
    



### Failure

Fails unless the theorem is contradictory, i.e. has `F` as its conclusion.

### See also

[`Tactic.CHECK_ASSUME_TAC`](#Tactic.CHECK_ASSUME_TAC), [`Drule.CONTR`](#Drule.CONTR), [`Thm.CCONTR`](#Thm.CCONTR), [`Drule.CONTRAPOS`](#Drule.CONTRAPOS), [`Thm.NOT_ELIM`](#Thm.NOT_ELIM)

