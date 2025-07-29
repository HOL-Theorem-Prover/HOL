## `PSTRIP_GOAL_THEN`

``` hol4
PairRules.PSTRIP_GOAL_THEN : (thm_tactic -> tactic)
```

------------------------------------------------------------------------

Splits a goal by eliminating one outermost connective, applying the
given theorem-tactic to the antecedents of implications.

Given a theorem-tactic `ttac` and a goal `(A,t)`, `PSTRIP_GOAL_THEN`
removes one outermost occurrence of one of the connectives `!`, `==>`,
`~` or `/\` from the conclusion of the goal `t`. If `t` is a universally
quantified term, then `STRIP_GOAL_THEN` strips off the quantifier. Note
that `PSTRIP_GOAL_THEN` will strip off paired universal quantifications.

``` hol4
      A ?- !p. u
   ==============  PSTRIP_GOAL_THEN ttac
    A ?- u[p'/p]
```

where `p'` is a primed variant that contains no variables that appear
free in the assumptions `A`. If `t` is a conjunction, then
`PSTRIP_GOAL_THEN` simply splits the conjunction into two subgoals:

``` hol4
      A ?- v /\ w
   =================  PSTRIP_GOAL_THEN ttac
    A ?- v   A ?- w
```

If `t` is an implication `"u ==> v"` and if:

``` hol4
      A ?- v
  ===============  ttac (u |- u)
     A' ?- v'
```

then:

``` hol4
      A ?- u ==> v
  ====================  PSTRIP_GOAL_THEN ttac
        A' ?- v'
```

Finally, a negation `~t` is treated as the implication `t ==> F`.

### Failure

`PSTRIP_GOAL_THEN ttac (A,t)` fails if `t` is not a paired universally
quantified term, an implication, a negation or a conjunction. Failure
also occurs if the application of `ttac` fails, after stripping the
goal.

`PSTRIP_GOAL_THEN` is used when manipulating intermediate results
(obtained by stripping outer connectives from a goal) directly, rather
than as assumptions.

### See also

[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`Tactic.STRIP_GOAL_THEN`](#Tactic.STRIP_GOAL_THEN),
[`PairRules.FILTER_PSTRIP_THEN`](#PairRules.FILTER_PSTRIP_THEN),
[`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC),
[`PairRules.FILTER_PSTRIP_TAC`](#PairRules.FILTER_PSTRIP_TAC)
