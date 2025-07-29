## `SUBST_MATCH`

``` hol4
Rewrite.SUBST_MATCH : (thm -> thm -> thm)
```

------------------------------------------------------------------------

Substitutes in one theorem using another, equational, theorem.

Given the theorems `A|-u=v` and `A'|-t`, `SUBST_MATCH (A|-u=v) (A'|-t)`
searches for one free instance of `u` in `t`, according to a top-down
left-to-right search strategy, and then substitutes the corresponding
instance of `v`.

``` hol4
    A |- u=v   A' |- t
   --------------------  SUBST_MATCH (A|-u=v) (A'|-t)
     A u A' |- t[v/u]
```

`SUBST_MATCH` allows only a free instance of `u` to be substituted for
in `t`. An instance which contain bound variables can be substituted for
by using rewriting rules such as `REWRITE_RULE`, `PURE_REWRITE_RULE` and
`ONCE_REWRITE_RULE`.

### Failure

`SUBST_MATCH th1 th2` fails if the conclusion of the theorem `th1` is
not an equation. Moreover, `SUBST_MATCH (A|-u=v) (A'|-t)` fails if no
instance of `u` occurs in `t`, since the matching algorithm fails. No
change is made to the theorem `(A'|-t)` if instances of `u` occur in
`t`, but they are not free (see `SUBS`).

### Example

The commutative law for addition

``` hol4
   - val thm1 = SPECL [Term `m:num`, Term `n:num`] arithmeticTheory.ADD_SYM;
   > val thm1 = |- m + n = n + m : thm
```

is used to apply substitutions, depending on the occurrence of free
instances

``` hol4
   - SUBST_MATCH thm1 (ASSUME (Term `(n + 1) + (m - 1) = m + n`));
   > val it =  [.] |- m - 1 + (n + 1) = m + n : thm

   - SUBST_MATCH thm1 (ASSUME (Term `!n. (n + 1) + (m - 1) = m + n`));
   > val it =  [.] |- !n. n + 1 + (m - 1) = m + n : thm
```

`SUBST_MATCH` is used when rewriting with the rules such as
`REWRITE_RULE`, using a single theorem is too extensive or would
diverge. Moreover, applying `SUBST_MATCH` can be much faster than using
the rewriting rules.

### See also

[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE),
[`Drule.SUBS`](#Drule.SUBS), [`Thm.SUBST`](#Thm.SUBST)
