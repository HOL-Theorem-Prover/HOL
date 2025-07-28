## `MP_TAC` {#Tactic.MP_TAC}


```
MP_TAC : thm_tactic
```



Reduces a goal to implication from a known theorem.


When applied to the theorem `A' |- s` and the goal `A ?- t`, the tactic
`MP_TAC` reduces the goal to `A ?- s ==> t`. Unless `A'` is a subset of
`A`, this is an invalid tactic.
    
           A ?- t
       ==============  MP_TAC (A' |- s)
        A ?- s ==> t
    



### Failure

Never fails.

### See also

[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC), [`Thm.MP`](#Thm.MP), [`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)

