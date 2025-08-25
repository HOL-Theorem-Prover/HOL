## `is_comb`

``` hol4
Term.is_comb : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a combination (function application).

If term `M` has the form `f x`, then `is_comb M` equals `true`.
Otherwise, the result is `false`.

### Failure

Never fails

### See also

[`Term.mk_comb`](#Term.mk_comb), [`Term.dest_comb`](#Term.dest_comb),
[`Term.is_var`](#Term.is_var), [`Term.is_const`](#Term.is_const),
[`Term.is_abs`](#Term.is_abs)
