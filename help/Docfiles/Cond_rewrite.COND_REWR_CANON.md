## `COND_REWR_CANON`

``` hol4
Cond_rewrite.COND_REWR_CANON : thm -> thm
```

------------------------------------------------------------------------

Transform a theorem into a form accepted by `COND_REWR_TAC`.

`COND_REWR_CANON` transforms a theorem into a form accepted by
`COND_REWR_TAC`. The input theorem should be an implication of the
following form

``` hol4
   !x1 ... xn. P1[xi] ==> ... ==> !y1 ... ym. Pr[xi,yi] ==>
     (!z1 ... zk. u[xi,yi,zi] = v[xi,yi,zi])
```

where each antecedent `Pi` itself may be a conjunction or disjunction.
The output theorem will have all universal quantifications moved to the
outer most level with possible renaming to prevent variable capture, and
have all antecedents which are a conjunction transformed to
implications. The output theorem will be in the following form

``` hol4
   !x1 ... xn y1 ... ym z1 ... zk.
    P11[xi] ==> ... ==> P1p[xi] ==> ... ==>
     Pr1[xi,yi] ==> ... ==> Prq[x1,yi] ==> (u[xi,yi,zi] = v[xi,yi,zi])
```

### Failure

This function fails if the input theorem is not in the correct form.

### Example

`COND_REWR_CANON` transforms the built-in theorem `CANCL_SUB` into the
form for conditional rewriting:

``` hol4
   #COND_REWR_CANON CANCEL_SUB;;
   Theorem CANCEL_SUB autoloading from theory `arithmetic` ...
   CANCEL_SUB = |- !p n m. p <= n /\ p <= m ==> ((n - p = m - p) = (n = m))

   |- !p n m. p <= n ==> p <= m ==> ((n - p = m - p) = (n = m))
```

### See also

[`Cond_rewrite.COND_REWRITE1_TAC`](#Cond_rewrite.COND_REWRITE1_TAC),
[`Cond_rewrite.COND_REWR_TAC`](#Cond_rewrite.COND_REWR_TAC),
[`Cond_rewrite.COND_REWRITE1_CONV`](#Cond_rewrite.COND_REWRITE1_CONV),
[`Cond_rewrite.COND_REWR_CONV`](#Cond_rewrite.COND_REWR_CONV),
[`Cond_rewrite.search_top_down`](#Cond_rewrite.search_top_down)
