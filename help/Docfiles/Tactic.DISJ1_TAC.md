## `DISJ1_TAC`

``` hol4
Tactic.DISJ1_TAC : tactic
```

------------------------------------------------------------------------

Selects the left disjunct of a disjunctive goal.

``` hol4
   A ?- t1 \/ t2
  ===============  DISJ1_TAC
     A ?- t1
```

### Failure

Fails if the goal is not a disjunction.

### See also

[`Thm.DISJ1`](#Thm.DISJ1), [`Thm.DISJ2`](#Thm.DISJ2),
[`Tactic.DISJ2_TAC`](#Tactic.DISJ2_TAC)
