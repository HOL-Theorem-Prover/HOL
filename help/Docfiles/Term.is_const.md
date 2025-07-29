## `is_const`

``` hol4
Term.is_const : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a constant.

If `c` is an instance of a previously declared HOL constant, then
`is_const c` returns `true`; otherwise the result is `false`.

### Failure

Never fails.

### See also

[`Term.mk_const`](#Term.mk_const),
[`Term.dest_const`](#Term.dest_const), [`Term.is_var`](#Term.is_var),
[`Term.is_comb`](#Term.is_comb), [`Term.is_abs`](#Term.is_abs)
