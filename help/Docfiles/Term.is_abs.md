## `is_abs`

``` hol4
Term.is_abs : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is an abstraction.

`is_abs "\var. t"` returns `true`. If the term is not an abstraction the
result is `false`.

### Failure

Never fails.

### See also

[`Term.mk_abs`](#Term.mk_abs), [`Term.dest_abs`](#Term.dest_abs),
[`Term.is_var`](#Term.is_var), [`Term.is_const`](#Term.is_const),
[`Term.is_comb`](#Term.is_comb)
