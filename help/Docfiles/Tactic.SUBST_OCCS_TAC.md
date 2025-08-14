## `SUBST_OCCS_TAC`

``` hol4
Tactic.SUBST_OCCS_TAC : (int list * thm) list -> tactic
```

------------------------------------------------------------------------

Makes substitutions in a goal at specific occurrences of a term, using a
list of theorems.

Given a list `(l1,A1|-t1=u1),...,(ln,An|-tn=un)` and a goal `(A,t)`,
`SUBST_OCCS_TAC` replaces each `ti` in `t` with `ui`, simultaneously, at
the occurrences specified by the integers in the list `li = [o1,...,ok]`
for each theorem `Ai|-ti=ui`.

``` hol4
              A ?- t
   =============================  SUBST_OCCS_TAC [(l1,A1|-t1=u1),...,
    A ?- t[u1,...,un/t1,...,tn]                   (ln,An|-tn=un)]
```

The assumptions of the theorems used to substitute with are not added to
the assumptions `A` of the goal, but they are recorded in the proof. If
any `Ai` is not a subset of `A` (up to alpha-conversion),
`SUBST_OCCS_TAC [(l1,A1|-t1=u1),...,(ln,An|-tn=un)]` results in an
invalid tactic.

`SUBST_OCCS_TAC` automatically renames bound variables to prevent free
variables in `ui` becoming bound after substitution.

### Failure

`SUBST_OCCS_TAC [(l1,th1),...,(ln,thn)] (A,t)` fails if the conclusion
of any theorem in the list is not an equation. No change is made to the
goal if the supplied occurrences `li` of the left-hand side of the
conclusion of `thi` do not appear in `t`.

### Example

When trying to solve the goal

``` hol4
   ?- (m + n) + (n + m) = (m + n) + (m + n)
```

applying the commutative law for addition on the third occurrence of the
subterm `m + n`

``` hol4
   SUBST_OCCS_TAC [([3], SPECL [Term `m:num`, Term `n:num`]
                               arithmeticTheory.ADD_SYM)]
```

results in the goal

``` hol4
   ?- (m + n) + (n + m) = (m + n) + (n + m)
```

`SUBST_OCCS_TAC` is used when rewriting a goal at specific occurrences
of a term, and when rewriting tactics such as `REWRITE_TAC`,
`PURE_REWRITE_TAC`, `ONCE_REWRITE_TAC`, `SUBST_TAC`, etc. are too
extensive or would diverge.

### See also

[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST1_TAC`](#Tactic.SUBST1_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
