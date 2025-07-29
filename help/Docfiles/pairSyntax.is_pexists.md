## `is_pexists`

``` hol4
pairSyntax.is_pexists : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it as a paired existential quantification.

`is_pexists "?pair. t"` returns `true`. If the term is not a paired
existential quantification the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.is_exists`](#boolSyntax.is_exists),
[`pairSyntax.dest_pexists`](#pairSyntax.dest_pexists)
