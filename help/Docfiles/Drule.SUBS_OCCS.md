## `SUBS_OCCS`

``` hol4
Drule.SUBS_OCCS : (int list * thm) list -> thm -> thm
```

------------------------------------------------------------------------

Makes substitutions in a theorem at specific occurrences of a term,
using a list of equational theorems.

Given a list `(l1,A1|-t1=v1),...,(ln,An|-tn=vn)` and a theorem `(A|-t)`,
`SUBS_OCCS` simultaneously replaces each `ti` in `t` with `vi`, at the
occurrences specified by the integers in the list `li = [o1,...,ok]` for
each theorem `Ai|-ti=vi`.

``` hol4
     (l1,A1|-t1=v1) ... (ln,An|-tn=vn)  A|-t
   -------------------------------------------  SUBS_OCCS[(l1,A1|-t1=v1),...,
    A1 u ... An u A |- t[v1,...,vn/t1,...,tn]            (ln,An|-tn=vn)] (A|-t)
```

### Failure

`SUBS_OCCS [(l1,th1),...,(ln,thn)] (A|-t)` fails if the conclusion of
any theorem in the list is not an equation. No change is made to the
theorem if the supplied occurrences `li` of the left-hand side of the
conclusion of `thi` do not appear in `t`.

### Example

The commutative law for addition

``` hol4
   - val thm = SPECL [Term `m:num`, Term`n:num`] arithmeticTheory.ADD_SYM;
   > val thm = |- m + n = n + m : thm
```

can be used for substituting only the second occurrence of the subterm
`m + n`

``` hol4
   - SUBS_OCCS [([2],thm)]
               (ASSUME (Term `(n + m) + (m + n) = (m + n) + (m + n)`));
   > val it =  [.] |- n + m + (m + n) = n + m + (m + n) : thm
```

`SUBS_OCCS` is used when rewriting at specific occurrences of a term,
and rules such as `REWRITE_RULE`, `PURE_REWRITE_RULE`,
`ONCE_REWRITE_RULE`, and `SUBS` are too extensive or would diverge.

### See also

[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE),
[`Drule.SUBS`](#Drule.SUBS), [`Thm.SUBST`](#Thm.SUBST),
[`Rewrite.SUBST_MATCH`](#Rewrite.SUBST_MATCH)
