## `mk_res_exists_unique`

``` hol4
res_quanLib.mk_res_exists_unique : (term # term # term) -> term
```

------------------------------------------------------------------------

Term constructor for restricted unique existential quantification.

`mk_res_exists_unique ("var","P","t")` returns `"?!var :: P . t"`.

### Failure

Fails with `mk_res_exists_unique` if the first term is not a variable or
if `P` and `t` are not of type `":bool"`.

### See also

[`res_quanLib.dest_res_exists_unique`](#res_quanLib.dest_res_exists_unique),
[`res_quanLib.is_res_exists_unique`](#res_quanLib.is_res_exists_unique)
