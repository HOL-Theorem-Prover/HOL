## `CONJ_TAC`

``` hol4
Tactic.CONJ_TAC : tactic
```

------------------------------------------------------------------------

Reduces a conjunctive goal to two separate subgoals.

When applied to a goal `A ?- t1 /\ t2`, the tactic `CONJ_TAC` reduces it
to the two subgoals corresponding to each conjunct separately.

``` hol4
       A ?- t1 /\ t2
   ======================  CONJ_TAC
    A ?- t1      A ?- t2
```

### Failure

Fails unless the conclusion of the goal is a conjunction.

### See also

[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC)
