## `CCONTR_TAC`

``` hol4
Tactic.CCONTR_TAC : tactic
```

------------------------------------------------------------------------

Assumes the negation of the conclusion of a goal.

Given a goal `A ?- t`, `CCONTR_TAC` makes a new goal which is to prove
`F` by assuming also the negation of the conclusion `t`.

``` hol4
     A ?- t
   ==========
   A, -t ?- F
```

### Failure

Never fails

### See also

[`Tactic.CHECK_ASSUME_TAC`](#Tactic.CHECK_ASSUME_TAC),
[`Thm.CCONTR`](#Thm.CCONTR), [`Drule.CONTRAPOS`](#Drule.CONTRAPOS),
[`Thm.NOT_ELIM`](#Thm.NOT_ELIM)
