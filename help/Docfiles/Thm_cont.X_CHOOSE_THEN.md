## `X_CHOOSE_THEN`

``` hol4
Thm_cont.X_CHOOSE_THEN : (term -> thm_tactical)
```

------------------------------------------------------------------------

Replaces existentially quantified variable with given witness, and
passes it to a theorem-tactic.

`X_CHOOSE_THEN` expects a variable `y`, a tactic-generating function
`f:thm->tactic`, and a theorem of the form `(A1 |- ?x. w)` as arguments.
A new theorem is created by introducing the given variable `y` as a
witness for the object `x` whose existence is asserted in the original
theorem, `(w[y/x] |- w[y/x])`. If the tactic-generating function `f`
applied to this theorem produces results as follows when applied to a
goal `(A ?- t)`:

``` hol4
    A ?- t
   =========  f ({w[y/x]} |- w[y/x])
    A ?- t1
```

then applying `(X_CHOOSE_THEN "y" f (A1 |- ?x. w))` to the goal
`(A ?- t)` produces the subgoal:

``` hol4
    A ?- t
   =========  X_CHOOSE_THEN y f (A1 |- ?x. w)
    A ?- t1         (y not free anywhere)
```

### Failure

Fails if the theorem's conclusion is not existentially quantified, or if
the first argument is not a variable. Failures may arise in the
tactic-generating function. An invalid tactic is produced if the
introduced variable is free in `w`, `t` or `A`, or if the theorem has
any hypothesis which is not alpha-convertible to an assumption of the
goal.

### Example

Given a goal of the form

``` hol4
   {n < m} ?- ?x. m = n + (x + 1)
```

the following theorem may be applied:

``` hol4
   th = [n < m] |- ?p. m = n + p
```

by the tactic `` (X_CHOOSE_THEN (Term`q:num`) SUBST1_TAC th) `` giving
the subgoal:

``` hol4
   {n < m} ?- ?x. n + q = n + (x + 1)
```

### See also

[`Thm.CHOOSE`](#Thm.CHOOSE),
[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`Thm_cont.CONJUNCTS_THEN`](#Thm_cont.CONJUNCTS_THEN),
[`Thm_cont.CONJUNCTS_THEN2`](#Thm_cont.CONJUNCTS_THEN2),
[`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN),
[`Thm_cont.DISJ_CASES_THEN2`](#Thm_cont.DISJ_CASES_THEN2),
[`Thm_cont.DISJ_CASES_THENL`](#Thm_cont.DISJ_CASES_THENL),
[`Thm_cont.STRIP_THM_THEN`](#Thm_cont.STRIP_THM_THEN),
[`Tactic.X_CHOOSE_TAC`](#Tactic.X_CHOOSE_TAC)
