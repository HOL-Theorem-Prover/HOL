## `RESQ_REWR_CANON`

``` hol4
res_quanLib.RESQ_REWR_CANON : thm -> thm
```

------------------------------------------------------------------------

Transform a theorem into a form accepted for rewriting.

`RESQ_REWR_CANON` transforms a theorem into a form accepted by
`COND_REWR_TAC`. The input theorem should be headed by a series of
restricted universal quantifications in the following form

``` hol4
   !x1::P1. ... !xn::Pn. u[xi] = v[xi])
```

Other variables occurring in `u` and `v` may be universally quantified.
The output theorem will have all ordinary universal quantifications
moved to the outer most level with possible renaming to prevent variable
capture, and have all restricted universal quantifications converted to
implications. The output theorem will be in the form accepted by
`COND_REWR_TAC`.

### Failure

This function fails is the input theorem is not in the correct form.

### See also

[`res_quanLib.RESQ_REWRITE1_TAC`](#res_quanLib.RESQ_REWRITE1_TAC),
[`res_quanLib.RESQ_REWRITE1_CONV`](#res_quanLib.RESQ_REWRITE1_CONV)
