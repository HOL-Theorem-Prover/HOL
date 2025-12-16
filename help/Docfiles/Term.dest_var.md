## `dest_var`

``` hol4
Term.dest_var : term -> string * hol_type
```

------------------------------------------------------------------------

Breaks apart a variable into name and type.

If `M` is a HOL variable, then `dest_var M` returns `(v,ty)`, where `v`
is the name of the variable, an `ty` is its type.

### Failure

Fails if `M` is not a variable.

### See also

[`Term.mk_var`](#Term.mk_var), [`Term.is_var`](#Term.is_var),
[`Term.dest_const`](#Term.dest_const),
[`Term.dest_comb`](#Term.dest_comb), [`Term.dest_abs`](#Term.dest_abs)
