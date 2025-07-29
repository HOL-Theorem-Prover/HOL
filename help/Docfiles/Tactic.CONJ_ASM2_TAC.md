## `CONJ_ASM2_TAC`

``` hol4
Tactic.CONJ_ASM2_TAC : tactic
```

------------------------------------------------------------------------

Reduces a conjunctive goal to two subgoals: prove the first conjunct
assuming the second, then prove the second conjunct.

When applied to a goal `A ?- t1 /\ t2`, the tactic `CONJ_ASM2_TAC`
reduces it to two subgoals corresponding to the two conjuncts, assuming
the first to prove the second.

``` hol4
         A ?- t1 /\ t2
   ==========================  CONJ_ASM2_TAC
    A u {t2} ?- t1   A ?- t2
```

### Failure

Fails unless the conclusion of the goal is a conjunction.

### See also

[`Tactic.CONJ_ASM1_TAC`](#Tactic.CONJ_ASM1_TAC),
[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Tactical.USE_SG_THEN`](#Tactical.USE_SG_THEN)
