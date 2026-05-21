## `SUBST_ALL_TAC`

``` hol4
Tactic.SUBST_ALL_TAC : thm_tactic
```

------------------------------------------------------------------------

Substitutes using a single equation in both the assumptions and
conclusion of a goal.

`SUBST_ALL_TAC` breaches the style of natural deduction, where the
assumptions are kept fixed. Given a theorem `A|-u=v` and a goal
`([t1;...;tn], t)`, `SUBST_ALL_TAC (A|-u=v)` transforms the assumptions
`t1`,...,`tn` and the term `t` into `t1[v/u]`,...,`tn[v/u]` and `t[v/u]`
respectively, by substituting `v` for each free occurrence of `u` in
both the assumptions and the conclusion of the goal.

``` hol4
           {t1,...,tn} ?- t
   =================================  SUBST_ALL_TAC (A|-u=v)
    {t1[v/u],...,tn[v/u]} ?- t[v/u]
```

The assumptions of the theorem used to substitute with are not added to
the assumptions of the goal, but they are recorded in the proof. If `A`
is not a subset of the assumptions of the goal (up to alpha-conversion),
then `SUBST_ALL_TAC (A|-u=v)` results in an invalid tactic.

`SUBST_ALL_TAC` automatically renames bound variables to prevent free
variables in `v` becoming bound after substitution.

### Failure

`SUBST_ALL_TAC th (A,t)` fails if the conclusion of `th` is not an
equation. No change is made to the goal if no occurrence of the
left-hand side of `th` appears free in `(A,t)`.

### Example

Simplifying both the assumption and the term in the goal

``` hol4
   {0 + m = n} ?- 0 + (0 + m) = n
```

by substituting with the theorem `|- 0 + m = m` for addition

``` hol4
   SUBST_ALL_TAC (CONJUNCT1 ADD_CLAUSES)
```

results in the goal

``` hol4
   {m = n} ?- 0 + m = n
```

### See also

[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST1_TAC`](#Tactic.SUBST1_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
