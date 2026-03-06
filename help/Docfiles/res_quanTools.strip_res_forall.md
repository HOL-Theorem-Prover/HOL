## `strip_res_forall`

``` hol4
res_quanTools.strip_res_forall : (term -> ((term # term) list # term))
```

------------------------------------------------------------------------

Iteratively breaks apart a restricted universally quantified term.

`strip_res_forall` is an iterative term destructor for restricted
universal quantifications. It iteratively breaks apart a restricted
universally quantified term into a list of pairs which are the
restricted quantified variables and predicates and the body.

``` hol4
   strip_res_forall "!x1::P1. ... !xn::Pn. t"
```

returns `([("x1","P1");...;("xn","Pn")],"t")`.

### Failure

Never fails.

### See also

[`res_quanTools.list_mk_res_forall`](#res_quanTools.list_mk_res_forall),
[`res_quanTools.is_res_forall`](#res_quanTools.is_res_forall),
[`res_quanTools.dest_res_forall`](#res_quanTools.dest_res_forall)
