## `dest_res_abstract`

``` hol4
res_quanLib.dest_res_abstract : term -> (term # term # term)
```

------------------------------------------------------------------------

Breaks apart a restricted abstract term into the quantified variable,
predicate and body.

`dest_res_abstract` is a term destructor for restricted abstraction:

``` hol4
   dest_res_abstract "\var::P. t"
```

returns `("var","P","t")`.

### Failure

Fails with `dest_res_abstract` if the term is not a restricted
abstraction.

### See also

[`res_quanLib.mk_res_abstract`](#res_quanLib.mk_res_abstract),
[`res_quanLib.is_res_abstract`](#res_quanLib.is_res_abstract)
