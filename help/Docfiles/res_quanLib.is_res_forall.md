## `is_res_forall`

``` hol4
res_quanLib.is_res_forall : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a restricted universal quantification.

`is_res_forall "!var::P. t"` returns `true`. If the term is not a
restricted universal quantification the result is `false`.

### Failure

Never fails.

### See also

[`res_quanLib.mk_res_forall`](#res_quanLib.mk_res_forall),
[`res_quanLib.dest_res_forall`](#res_quanLib.dest_res_forall)
