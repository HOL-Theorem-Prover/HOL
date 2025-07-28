## `IRULE_CANON` {#Drule.IRULE_CANON}


```
IRULE_CANON : thm -> thm
```



Canonicalises a theorem for use as an introduction rule.


A call to `IRULE_CANON th` returns a theorem `th'` that is equivalent
to `th`, but syntactically rearranged to be in the form
    
       !v1 .. vn. c1 /\ c2 ... /\ cm ==> c
    
(also allowing for no conjuncts at all). The variables `v1` to `vn`
all occur in the conclusion `c`, which is not universally quantified,
nor an implication.

Each of the conjuncts is of the form
    
       ?ev1 .. evi. ec1 /\ .. ecj
    
where it is possible that there are not existentially quantified
variables. The existential quantification ensures that there are no free variables in the output theorem `th'`.

### Failure

Never fails.

### Comments

This function is used within the implementation of `irule`. The output
theorem `th'` is appropriate for use as an argument to `MATCH_MP_TAC`
(if the output is a quantified implication), or `MATCH_ACCEPT_TAC` if
the output is not an implication.

### See also

[`Tactic.irule`](#Tactic.irule), [`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC), [`Drule.RES_CANON`](#Drule.RES_CANON)

