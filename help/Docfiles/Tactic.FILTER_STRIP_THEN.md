## `FILTER_STRIP_THEN`

``` hol4
Tactic.FILTER_STRIP_THEN : (thm_tactic -> term -> tactic)
```

------------------------------------------------------------------------

Conditionally strips a goal, handing an antecedent to the
theorem-tactic.

Given a theorem-tactic `ttac`, a term `u` and a goal `(A,t)`,
`FILTER_STRIP_THEN ttac u` removes one outer connective (`!`, `==>`, or
`~`) from `t`, if the term being stripped does not contain a free
instance of `u`. A negation `~t` is treated as the implication
`t ==> F`. The theorem-tactic `ttac` is applied only when stripping an
implication, by using the antecedent stripped off. `FILTER_STRIP_THEN`
also breaks conjunctions.

`FILTER_STRIP_THEN` behaves like `STRIP_GOAL_THEN`, if the term being
stripped does not contain a free instance of `u`. In particular,
`FILTER_STRIP_THEN STRIP_ASSUME_TAC` behaves like `FILTER_STRIP_TAC`.

### Failure

`FILTER_STRIP_THEN ttac u (A,t)` fails if `t` is not a universally
quantified term, an implication, a negation or a conjunction; or if the
term being stripped contains the term `u` (conjunction excluded); or if
the application of `ttac` fails, after stripping the goal.

### Example

When solving the goal

``` hol4
   ?- (n = 1) ==> (n * n = n)
```

the application of `FILTER_STRIP_THEN SUBST1_TAC "m:num"` results in the
goal

``` hol4
   ?- 1 * 1 = 1
```

`FILTER_STRIP_THEN` is used when manipulating intermediate results using
theorem-tactics, after stripping outer connectives from a goal in a more
delicate way than `STRIP_GOAL_THEN`.

### See also

[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Tactic.FILTER_GEN_TAC`](#Tactic.FILTER_GEN_TAC),
[`Tactic.FILTER_STRIP_TAC`](#Tactic.FILTER_STRIP_TAC),
[`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC),
[`Tactic.STRIP_GOAL_THEN`](#Tactic.STRIP_GOAL_THEN)
