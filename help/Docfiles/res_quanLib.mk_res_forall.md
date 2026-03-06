## `mk_res_forall`

``` hol4
res_quanLib.mk_res_forall : (term # term # term) -> term
```

------------------------------------------------------------------------

Term constructor for restricted universal quantification.

`mk_res_forall("var","P","t")` returns `"!var :: P . t"`.

### Failure

Fails with `mk_res_forall` if the first term is not a variable or if `P`
and `t` are not of type `":bool"`.

### See also

[`res_quanLib.dest_res_forall`](#res_quanLib.dest_res_forall),
[`res_quanLib.is_res_forall`](#res_quanLib.is_res_forall),
[`res_quanLib.list_mk_res_forall`](#res_quanLib.list_mk_res_forall)
