## `list_mk_res_forall`

``` hol4
res_quanLib.list_mk_res_forall : (term # term) list # term) -> term
```

------------------------------------------------------------------------

Iteratively constructs a restricted universal quantification.

``` hol4
   list_mk_res_forall([("x1","P1");...;("xn","Pn")],"t")
```

returns `"!x1::P1. ... !xn::Pn. t"`.

### Failure

Fails with `list_mk_res_forall` if the first terms `xi` in the pairs are
not a variable or if the second terms `Pi` in the pairs and `t` are not
of type `":bool"` if the list is non-empty. If the list is empty the
type of `t` can be anything.

### See also

[`res_quanLib.strip_res_forall`](#res_quanLib.strip_res_forall),
[`res_quanLib.mk_res_forall`](#res_quanLib.mk_res_forall)
