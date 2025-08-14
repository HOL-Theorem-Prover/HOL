## `SUBST_TAC`

``` hol4
Tactic.SUBST_TAC : (thm list -> tactic)
```

------------------------------------------------------------------------

Makes term substitutions in a goal using a list of theorems.

Given a list of theorems `A1|-u1=v1,...,An|-un=vn` and a goal `(A,t)`,
`SUBST_TAC` rewrites the term `t` into the term `t[v1,...,vn/u1,...,un]`
by simultaneously substituting `vi` for each occurrence of `ui` in `t`
with `vi`:

``` hol4
              A ?- t
   =============================  SUBST_TAC [A1|-u1=v1,...,An|-un=vn]
    A ?- t[v1,...,vn/u1,...,un]
```

The assumptions of the theorems used to substitute with are not added to
the assumptions `A` of the goal, while they are recorded in the proof.
If any `Ai` is not a subset of `A` (up to alpha-conversion), then
`SUBST_TAC [A1|-u1=v1,...,An|-un=vn]` results in an invalid tactic.

`SUBST_TAC` automatically renames bound variables to prevent free
variables in `vi` becoming bound after substitution.

### Failure

`SUBST_TAC [th1,...,thn] (A,t)` fails if the conclusion of any theorem
in the list is not an equation. No change is made to the goal if no
occurrence of the left-hand side of the conclusion of `thi` appears in
`t`.

### Example

When trying to solve the goal

``` hol4
   ?- (n + 0) + (0 + m) = m + n
```

by substituting with the theorems

``` hol4
   - val thm1 = SPEC_ALL arithmeticTheory.ADD_SYM
     val thm2 = CONJUNCT1 arithmeticTheory.ADD_CLAUSES;
   thm1 = |- m + n = n + m
   thm2 = |- 0 + m = m
```

applying `SUBST_TAC [thm1, thm2]` results in the goal

``` hol4
   ?- (n + 0) + m = n + m
```

`SUBST_TAC` is used when rewriting (for example, with `REWRITE_TAC`) is
extensive or would diverge. Substituting is also much faster than
rewriting.

### See also

[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST1_TAC`](#Tactic.SUBST1_TAC),
[`Tactic.SUBST_ALL_TAC`](#Tactic.SUBST_ALL_TAC)
