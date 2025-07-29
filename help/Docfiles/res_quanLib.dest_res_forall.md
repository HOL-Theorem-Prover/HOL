## `dest_res_forall`

``` hol4
res_quanLib.dest_res_forall : term -> (term # term # term)
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

[`res_quanLib.mk_res_forall`](#res_quanLib.mk_res_forall),
[`res_quanLib.is_res_forall`](#res_quanLib.is_res_forall),
[`res_quanLib.strip_res_forall`](#res_quanLib.strip_res_forall)
