## `mk_res_exists`

``` hol4
res_quanLib.mk_res_exists : ((term # term # term) -> term)
```

------------------------------------------------------------------------

Term constructor for restricted existential quantification.

`mk_res_exists("var","P","t")` returns `"?var :: P . t"`.

### Failure

Fails with `mk_res_exists` if the first term is not a variable or if `P`
and `t` are not of type `":bool"`.

### See also

[`res_quanLib.dest_res_exists`](#res_quanLib.dest_res_exists),
[`res_quanLib.is_res_exists`](#res_quanLib.is_res_exists),
[`res_quanLib.list_mk_res_exists`](#res_quanLib.list_mk_res_exists)
