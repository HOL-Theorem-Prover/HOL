## `list_mk_res_forall` {#res_quanTools.list_mk_res_forall}


```
list_mk_res_forall : ((term # term) list # term) -> term)
```



Iteratively constructs a restricted universal quantification.


    
       list_mk_res_forall([("x1","P1");...;("xn","Pn")],"t")
    
returns `"!x1::P1. ... !xn::Pn. t"`.

### Failure

Fails with `list_mk_res_forall` if the first terms `xi` in the pairs are
not a variable or if the second terms `Pi` in the pairs and `t`
are not of type `":bool"` if the list is non-empty. If the list is
empty the type of `t` can be anything.

### See also

[`res_quanTools.strip_res_forall`](#res_quanTools.strip_res_forall), [`res_quanTools.mk_res_forall`](#res_quanTools.mk_res_forall)

