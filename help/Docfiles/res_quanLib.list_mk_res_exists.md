## `list_mk_res_exists`

``` hol4
res_quanLib.list_mk_res_exists : ((term # term) list # term) -> term)
```

------------------------------------------------------------------------

Iteratively constructs a restricted existential quantification.

``` hol4
   list_mk_res_exists([("x1","P1");...;("xn","Pn")],"t")
```

returns `"?x1::P1. ... ?xn::Pn. t"`.

### Failure

Fails with `list_mk_res_exists` if the first terms `xi` in the pairs are
not a variable or if the second terms `Pi` in the pairs and `t` are not
of type `":bool"` if the list is non-empty. If the list is empty the
type of `t` can be anything.

### See also

[`res_quanLib.strip_res_exists`](#res_quanLib.strip_res_exists),
[`res_quanLib.mk_res_exists`](#res_quanLib.mk_res_exists)
