## `is_exists`

``` hol4
boolSyntax.is_exists : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is an existential quantification.

If `M` has the form `?v. t` then `is_exists M` returns `true`. If the
term is not an existential quantification the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_exists`](#boolSyntax.mk_exists),
[`boolSyntax.dest_exists`](#boolSyntax.dest_exists)
