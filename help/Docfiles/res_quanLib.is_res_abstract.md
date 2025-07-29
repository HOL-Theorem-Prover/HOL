## `is_res_abstract`

``` hol4
res_quanLib.is_res_abstract : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a restricted abstraction.

`is_res_abstract "\var::P. t"` returns `true`. If the term is not a
restricted abstraction the result is `false`.

### Failure

Never fails.

### See also

[`res_quanLib.mk_res_abstract`](#res_quanLib.mk_res_abstract),
[`res_quanLib.dest_res_abstract`](#res_quanLib.dest_res_abstract)
