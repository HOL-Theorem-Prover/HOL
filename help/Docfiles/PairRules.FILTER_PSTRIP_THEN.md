## `FILTER_PSTRIP_THEN`

``` hol4
PairRules.FILTER_PSTRIP_THEN : (thm_tactic -> term -> tactic)
```

------------------------------------------------------------------------

Conditionally strips a goal, handing an antecedent to the
theorem-tactic.

Given a theorem-tactic `ttac`, a term `u` and a goal `(A,t)`,
`FILTER_STRIP_THEN ttac u` removes one outer connective (`!`, `==>`, or
`~`) from `t`, if the term being stripped does not contain a free
instance of `u`. Note that `FILTER_PSTRIP_THEN` will strip paired
universal quantifiers. A negation `~t` is treated as the implication
`t ==> F`. The theorem-tactic `ttac` is applied only when stripping an
implication, by using the antecedent stripped off. `FILTER_PSTRIP_THEN`
also breaks conjunctions.

`FILTER_PSTRIP_THEN` behaves like `PSTRIP_GOAL_THEN`, if the term being
stripped does not contain a free instance of `u`. In particular,
`FILTER_PSTRIP_THEN PSTRIP_ASSUME_TAC` behaves like `FILTER_PSTRIP_TAC`.

### Failure

`FILTER_PSTRIP_THEN ttac u (A,t)` fails if `t` is not a paired
universally quantified term, an implication, a negation or a
conjunction; or if the term being stripped contains the term `u`
(conjunction excluded); or if the application of `ttac` fails, after
stripping the goal.

`FILTER_PSTRIP_THEN` is used to manipulate intermediate results using
theorem-tactics, after stripping outer connectives from a goal in a more
delicate way than `PSTRIP_GOAL_THEN`.

### See also

[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSTRIP_GOAL_THEN`](#PairRules.PSTRIP_GOAL_THEN),
[`Tactic.FILTER_STRIP_THEN`](#Tactic.FILTER_STRIP_THEN),
[`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC),
[`PairRules.FILTER_PSTRIP_TAC`](#PairRules.FILTER_PSTRIP_TAC)
