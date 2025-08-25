## `DISJ2_TAC`

``` hol4
Tactic.DISJ2_TAC : tactic
```

------------------------------------------------------------------------

Selects the right disjunct of a disjunctive goal.

``` hol4
    A ?- t1 \/ t2
   ===============  DISJ2_TAC
       A ?- t2
```

### Failure

Fails if the goal is not a disjunction.

### See also

[`Thm.DISJ1`](#Thm.DISJ1), [`Tactic.DISJ1_TAC`](#Tactic.DISJ1_TAC),
[`Thm.DISJ2`](#Thm.DISJ2)
