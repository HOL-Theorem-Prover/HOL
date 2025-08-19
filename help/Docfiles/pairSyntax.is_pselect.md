## `is_pselect`

``` hol4
pairSyntax.is_pselect : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is a paired choice-term.

`is_select "@pair. t"` returns `true`. If the term is not a paired
choice-term the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.is_select`](#boolSyntax.is_select),
[`pairSyntax.dest_pselect`](#pairSyntax.dest_pselect)
