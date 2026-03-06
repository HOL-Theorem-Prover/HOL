## `dest_comb`

``` hol4
Term.dest_comb : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a combination (function application) into rator and rand.

`dest_comb` is a term destructor for combinations. If term `M` has the
form `f x`, then `dest_comb M` equals `(f,x)`.

### Failure

Fails if the argument is not a function application.

### See also

[`Term.mk_comb`](#Term.mk_comb), [`Term.is_comb`](#Term.is_comb),
[`Term.dest_var`](#Term.dest_var),
[`Term.dest_const`](#Term.dest_const),
[`Term.dest_abs`](#Term.dest_abs),
[`boolSyntax.strip_comb`](#boolSyntax.strip_comb)
