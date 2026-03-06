## `SUBST1_TAC`

``` hol4
Tactic.SUBST1_TAC : thm_tactic
```

------------------------------------------------------------------------

Makes a simple term substitution in a goal using a single equational
theorem.

Given a theorem `A'|-u=v` and a goal `(A,t)`, the tactic
`SUBST1_TAC (A'|-u=v)` rewrites the term `t` into `t[v/u]`, by
substituting `v` for each free occurrence of `u` in `t`:

``` hol4
      A ?- t
   =============  SUBST1_TAC (A'|-u=v)
    A ?- t[v/u]
```

The assumptions of the theorem used to substitute with are not added to
the assumptions of the goal but are recorded in the proof. If `A'` is
not a subset of the assumptions `A` of the goal (up to
alpha-conversion), then `SUBST1_TAC (A'|-u=v)` results in an invalid
tactic.

`SUBST1_TAC` automatically renames bound variables to prevent free
variables in `v` becoming bound after substitution.

### Failure

`SUBST1_TAC th (A,t)` fails if the conclusion of `th` is not an
equation. No change is made to the goal if no free occurrence of the
left-hand side of `th` appears in `t`.

### Example

When trying to solve the goal

``` hol4
   ?- m * n = (n * (m - 1)) + n
```

substituting with the commutative law for multiplication

``` hol4
   SUBST1_TAC (SPECL ["m:num"; "n:num"] MULT_SYM)
```

results in the goal

``` hol4
   ?- n * m = (n * (m - 1)) + n
```

`SUBST1_TAC` is used when rewriting with a single theorem using tactics
such as `REWRITE_TAC` is too expensive or would diverge. Applying
`SUBST1_TAC` is also much faster than using rewriting tactics.

### See also

[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST_ALL_TAC`](#Tactic.SUBST_ALL_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
