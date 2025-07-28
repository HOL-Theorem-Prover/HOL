## `FULL_STRUCT_CASES_TAC` {#Tactic.FULL_STRUCT_CASES_TAC}


```
FULL_STRUCT_CASES_TAC : thm_tactic
```



A form of `STRUCT_CASES_TAC` that also applies the case analysis to the assumption list.


See `STRUCT_CASES_TAC`.

### Failure

Fails unless provided with a theorem that is a conjunction of
(possibly multiply existentially quantified) terms which assert the equality
of a variable with some given terms.

### Example

Suppose we have the goal:
    
      ~(l:(*)list = []) ?- (LENGTH l) > 0
    
then we can get rid of the universal quantifier from the
inbuilt list theorem `list_CASES`:
    
       list_CASES = !l. (l = []) \/ (?t h. l = CONS h t)
    
and then use `FULL_STRUCT_CASES_TAC`. This amounts to applying the
following tactic:
    
       FULL_STRUCT_CASES_TAC (SPEC_ALL list_CASES)
    
which results in the following two subgoals:
    
       ~(CONS h t = []) ?- (LENGTH(CONS h t)) > 0
    
       ~([] = []) ?- (LENGTH[]) > 0
    
Note that this is a rather simple case, since there are no
constraints, and therefore the resulting subgoals have no extra assumptions.


Generating a case split from the axioms specifying a structure.

### See also

[`Tactic.ASM_CASES_TAC`](#Tactic.ASM_CASES_TAC), [`Tactic.BOOL_CASES_TAC`](#Tactic.BOOL_CASES_TAC), [`Tactic.COND_CASES_TAC`](#Tactic.COND_CASES_TAC), [`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC), [`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC)

