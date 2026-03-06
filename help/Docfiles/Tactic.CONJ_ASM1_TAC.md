## `CONJ_ASM1_TAC`

``` hol4
Tactic.CONJ_ASM1_TAC : tactic
```

------------------------------------------------------------------------

Reduces a conjunctive goal to two subgoals: prove the first conjunct,
then the second assuming the first.

When applied to a goal `A ?- t1 /\ t2`, the tactic `CONJ_ASM1_TAC`
reduces it to two subgoals corresponding to the first conjunct then the
second conjunct.

``` hol4
         A ?- t1 /\ t2
   ==========================  CONJ_ASM1_TAC
    A ?- t1   A u {t1} ?- t2
```

### Failure

Fails unless the conclusion of the goal is a conjunction.

### See also

[`Tactic.CONJ_ASM2_TAC`](#Tactic.CONJ_ASM2_TAC),
[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Tactical.USE_SG_THEN`](#Tactical.USE_SG_THEN)
