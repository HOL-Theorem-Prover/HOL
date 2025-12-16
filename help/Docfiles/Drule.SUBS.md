## `SUBS`

``` hol4
Drule.SUBS : (thm list -> thm -> thm)
```

------------------------------------------------------------------------

Makes simple term substitutions in a theorem using a given list of
theorems.

Term substitution in HOL is performed by replacing free subterms
according to the transformations specified by a list of equational
theorems. Given a list of theorems `A1|-t1=v1,...,An|-tn=vn` and a
theorem `A|-t`, `SUBS` simultaneously replaces each free occurrence of
`ti` in `t` with `vi`:

``` hol4
          A1|-t1=v1 ... An|-tn=vn    A|-t
   ---------------------------------------------  SUBS[A1|-t1=v1;...;An|-tn=vn]
    A1 u ... u An u A |- t[v1,...,vn/t1,...,tn]       (A|-t)
```

No matching is involved; the occurrence of each `ti` being substituted
for must be a free in `t` (see `SUBST_MATCH`). An occurrence which is
not free can be substituted by using rewriting rules such as
`REWRITE_RULE`, `PURE_REWRITE_RULE` and `ONCE_REWRITE_RULE`.

### Failure

`SUBS [th1,...,thn] (A|-t)` fails if the conclusion of each theorem in
the list is not an equation. No change is made to the theorem `A |- t`
if no occurrence of any left-hand side of the supplied equations appears
in `t`.

### Example

Substitutions are made with the theorems

``` hol4
   - val thm1 = SPECL [Term`m:num`, Term`n:num`] arithmeticTheory.ADD_SYM
     val thm2 = CONJUNCT1 arithmeticTheory.ADD_CLAUSES;
   > val thm1 = |- m + n = n + m : thm
     val thm2 = |- 0 + m = m : thm
```

depending on the occurrence of free subterms

``` hol4
   - SUBS [thm1, thm2] (ASSUME (Term `(n + 0) + (0 + m) = m + n`));
   > val it =  [.] |- n + 0 + m = n + m : thm

   - SUBS [thm1, thm2] (ASSUME (Term `!n. (n + 0) + (0 + m) = m + n`));
   > val it =  [.] |- !n. n + 0 + m = m + n : thm
```

`SUBS` can sometimes be used when rewriting (for example, with
`REWRITE_RULE`) would diverge and term instantiation is not needed.
Moreover, applying the substitution rules is often much faster than
using the rewriting rules.

### See also

[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE),
[`Thm.SUBST`](#Thm.SUBST),
[`Rewrite.SUBST_MATCH`](#Rewrite.SUBST_MATCH),
[`Drule.SUBS_OCCS`](#Drule.SUBS_OCCS)
