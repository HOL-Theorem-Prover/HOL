## `strip_res_exists`

``` hol4
res_quanLib.strip_res_exists : (term -> ((term # term) list # term))
```

------------------------------------------------------------------------

Iteratively breaks apart a restricted existentially quantified term.

`strip_res_exists` is an iterative term destructor for restricted
existential quantifications. It iteratively breaks apart a restricted
existentially quantified term into a list of pairs which are the
restricted quantified variables and predicates and the body.

``` hol4
   strip_res_exists "?x1::P1. ... ?xn::Pn. t"
```

returns `([("x1","P1");...;("xn","Pn")],"t")`.

### Failure

Never fails.

### See also

[`res_quanLib.list_mk_res_exists`](#res_quanLib.list_mk_res_exists),
[`res_quanLib.is_res_exists`](#res_quanLib.is_res_exists),
[`res_quanLib.dest_res_exists`](#res_quanLib.dest_res_exists)
