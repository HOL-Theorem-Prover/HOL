## `is_res_select`

``` hol4
res_quanTools.is_res_select : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is a restricted choice quantification.

`is_res_select "@var::P. t"` returns `true`. If the term is not a
restricted choice quantification the result is `false`.

### Failure

Never fails.

### See also

[`res_quanTools.mk_res_select`](#res_quanTools.mk_res_select),
[`res_quanTools.dest_res_select`](#res_quanTools.dest_res_select)
