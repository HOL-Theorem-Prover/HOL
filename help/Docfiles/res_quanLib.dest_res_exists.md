## `dest_res_exists`

``` hol4
res_quanLib.dest_res_exists : term -> (term # term # term)
```

------------------------------------------------------------------------

Breaks apart a restricted existentially quantified term into the
quantified variable, predicate and body.

`dest_res_exists` is a term destructor for restricted existential
quantification:

``` hol4
   dest_res_exists "?var::P. t"
```

returns `("var","P","t")`.

### Failure

Fails with `dest_res_exists` if the term is not a restricted existential
quantification.

### See also

[`res_quanLib.mk_res_exists`](#res_quanLib.mk_res_exists),
[`res_quanLib.is_res_exists`](#res_quanLib.is_res_exists),
[`res_quanLib.strip_res_exists`](#res_quanLib.strip_res_exists)
