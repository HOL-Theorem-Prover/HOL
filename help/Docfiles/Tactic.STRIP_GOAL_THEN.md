## `STRIP_GOAL_THEN`

``` hol4
Tactic.STRIP_GOAL_THEN : thm_tactic -> tactic
```

------------------------------------------------------------------------

Splits a goal by eliminating one outermost connective, applying the
given theorem-tactic to the antecedents of implications.

Given a theorem-tactic `ttac` and a goal `(A,t)`, `STRIP_GOAL_THEN`
removes one outermost occurrence of one of the connectives `!`, `==>`,
`~` or `/\` from the conclusion of the goal `t`. If `t` is a universally
quantified term, then `STRIP_GOAL_THEN` strips off the quantifier:

``` hol4
      A ?- !x.u
   ==============  STRIP_GOAL_THEN ttac
     A ?- u[x'/x]
```

where `x'` is a primed variant that does not appear free in the
assumptions `A`. If `t` is a conjunction, then `STRIP_GOAL_THEN` simply
splits the conjunction into two subgoals:

``` hol4
      A ?- v /\ w
   =================  STRIP_GOAL_THEN ttac
    A ?- v   A ?- w
```

If `t` is an implication `u ==> v` and if:

``` hol4
      A ?- v
  ===============  ttac (u |- u)
     A' ?- v'
```

then:

``` hol4
      A ?- u ==> v
  ====================  STRIP_GOAL_THEN ttac
        A' ?- v'
```

Finally, a negation `~t` is treated as the implication `t ==> F`.

### Failure

`STRIP_GOAL_THEN ttac (A,t)` fails if `t` is not a universally
quantified term, an implication, a negation or a conjunction. Failure
also occurs if the application of `ttac` fails, after stripping the
goal.

### Example

When solving the goal

``` hol4
   ?- (n = 1) ==> (n * n = n)
```

a possible initial step is to apply

``` hol4
   STRIP_GOAL_THEN SUBST1_TAC
```

thus obtaining the goal

``` hol4
   ?- 1 * 1 = 1
```

`STRIP_GOAL_THEN` is used when manipulating intermediate results
(obtained by stripping outer connectives from a goal) directly, rather
than as assumptions.

### See also

[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Tactic.FILTER_STRIP_THEN`](#Tactic.FILTER_STRIP_THEN),
[`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC)
