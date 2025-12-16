## `mk_res_abstract`

``` hol4
res_quanTools.mk_res_abstract : ((term # term # term) -> term)
```

------------------------------------------------------------------------

Term constructor for restricted abstraction.

`mk_res_abstract("var","P","t")` returns `"\var :: P . t"`.

### Failure

Fails with `mk_res_abstract` if the first term is not a variable or if
`P` and `t` are not of type `":bool"`.

### See also

[`res_quanTools.dest_res_abstract`](#res_quanTools.dest_res_abstract),
[`res_quanTools.is_res_abstract`](#res_quanTools.is_res_abstract)
