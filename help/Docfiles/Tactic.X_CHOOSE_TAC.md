## `X_CHOOSE_TAC`

``` hol4
Tactic.X_CHOOSE_TAC : term -> thm_tactic
```

------------------------------------------------------------------------

Assumes a theorem, with existentially quantified variable replaced by a
given witness.

`X_CHOOSE_TAC` expects a variable `y` and theorem with an existentially
quantified conclusion. When applied to a goal, it adds a new assumption
obtained by introducing the variable `y` as a witness for the object `x`
whose existence is asserted in the theorem.

``` hol4
           A ?- t
   ===================  X_CHOOSE_TAC y (A1 |- ?x. w)
    A u {w[y/x]} ?- t         (y not free anywhere)
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

by the tactic `` (X_CHOOSE_TAC (Term`q:num`) th) `` giving the subgoal:

``` hol4
   {n < m, m = n + q} ?- ?x. m = n + (x + 1)
```

### See also

[`Thm.CHOOSE`](#Thm.CHOOSE),
[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`Thm_cont.X_CHOOSE_THEN`](#Thm_cont.X_CHOOSE_THEN)
