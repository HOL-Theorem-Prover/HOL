## `dest_res_select`

``` hol4
res_quanLib.dest_res_select : term -> (term # term # term)
```

------------------------------------------------------------------------

Breaks apart a restricted choice quantified term into the quantified
variable, predicate and body.

`dest_res_select` is a term destructor for restricted choice
quantification:

``` hol4
   dest_res_select "@var::P. t"
```

returns `("var","P","t")`.

### Failure

Fails with `dest_res_select` if the term is not a restricted choice
quantification.

### See also

[`res_quanLib.mk_res_select`](#res_quanLib.mk_res_select),
[`res_quanLib.is_res_select`](#res_quanLib.is_res_select)
