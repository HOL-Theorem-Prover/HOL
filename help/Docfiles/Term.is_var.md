## `is_var`

``` hol4
Term.is_var : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a variable.

If `M` is a HOL variable, then `is_var M` returns `true`. If the term is
not a variable the result is `false`.

### Failure

Never fails.

### See also

[`Term.mk_var`](#Term.mk_var), [`Term.dest_var`](#Term.dest_var),
[`Term.is_const`](#Term.is_const), [`Term.is_comb`](#Term.is_comb),
[`Term.is_abs`](#Term.is_abs)
