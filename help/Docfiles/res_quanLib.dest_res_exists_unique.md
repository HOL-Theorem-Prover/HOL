## `dest_res_exists_unique`

``` hol4
res_quanLib.dest_res_exists_unique : term -> (term # term # term)
```

------------------------------------------------------------------------

Breaks apart a restricted unique existential quantified term into the
quantified variable, predicate and body.

`dest_res_exists_unique` is a term destructor for restricted existential
quantification:

``` hol4
   dest_res_exists_unique "?var::P. t"
```

returns `("var","P","t")`.

### Failure

Fails with `dest_res_exists_unique` if the term is not a restricted
existential quantification.

### See also

[`res_quanLib.mk_res_exists_unique`](#res_quanLib.mk_res_exists_unique),
[`res_quanLib.is_res_exists_unique`](#res_quanLib.is_res_exists_unique)
