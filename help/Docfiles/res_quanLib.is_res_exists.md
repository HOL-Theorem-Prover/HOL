## `is_res_exists`

``` hol4
res_quanLib.is_res_exists : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a restricted existential quantification.

`is_res_exists "?var::P. t"` returns `true`. If the term is not a
restricted existential quantification the result is `false`.

### Failure

Never fails.

### See also

[`res_quanLib.mk_res_exists`](#res_quanLib.mk_res_exists),
[`res_quanLib.dest_res_exists`](#res_quanLib.dest_res_exists)
