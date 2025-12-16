## `is_res_exists_unique`

``` hol4
res_quanLib.is_res_exists_unique : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a restricted unique existential
quantification.

`is_res_exists_unique "?!var::P. t"` returns `true`. If the term is not
a restricted unique existential quantification the result is `false`.

### Failure

Never fails.

### See also

[`res_quanLib.mk_res_exists_unique`](#res_quanLib.mk_res_exists_unique),
[`res_quanLib.dest_res_exists_unique`](#res_quanLib.dest_res_exists_unique)
