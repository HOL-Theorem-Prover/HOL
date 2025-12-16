## `is_exists1`

``` hol4
boolSyntax.is_exists1 : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a unique existence term.

If `M` has the form `?!v. t` then `is_exists1 M` returns `true`. If the
term is not a unique existence quantification the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_exists1`](#boolSyntax.mk_exists1),
[`boolSyntax.dest_exists`](#boolSyntax.dest_exists)
