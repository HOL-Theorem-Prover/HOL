## `dest_res_forall`

``` hol4
res_quanTools.dest_res_forall : (term -> (term # term # term))
```

------------------------------------------------------------------------

Breaks apart a restricted universally quantified term into the
quantified variable, predicate and body.

`dest_res_forall` is a term destructor for restricted universal
quantification:

``` hol4
   dest_res_forall "!var::P. t"
```

returns `("var","P","t")`.

### Failure

Fails with `dest_res_forall` if the term is not a restricted universal
quantification.

### See also

[`res_quanTools.mk_res_forall`](#res_quanTools.mk_res_forall),
[`res_quanTools.is_res_forall`](#res_quanTools.is_res_forall),
[`res_quanTools.strip_res_forall`](#res_quanTools.strip_res_forall)
