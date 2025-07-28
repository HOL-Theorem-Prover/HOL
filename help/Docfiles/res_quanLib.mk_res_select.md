## `mk_res_select` {#res_quanLib.mk_res_select}


```
mk_res_select : (term # term # term) -> term
```



Term constructor for restricted choice quantification.


`mk_res_select("var","P","t")` returns `"@var :: P . t"`.

### Failure

Fails with `mk_res_select` if the first term is not a variable or if `P` and `t`
are not of type `":bool"`.

### See also

[`res_quanLib.dest_res_select`](#res_quanLib.dest_res_select), [`res_quanLib.is_res_select`](#res_quanLib.is_res_select)

