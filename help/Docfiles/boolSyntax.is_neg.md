## `is_neg`

``` hol4
boolSyntax.is_neg : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a negation.

If `M` has the form `~t`, then `is_neg M` returns `true`. If the term is
not a negation the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_neg`](#boolSyntax.mk_neg),
[`boolSyntax.dest_neg`](#boolSyntax.dest_neg)
