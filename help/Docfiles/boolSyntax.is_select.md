## `is_select`

``` hol4
boolSyntax.is_select : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is a choice binding.

`is_select "@var. t"` returns `true`. If the term is not an epsilon-term
the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_select`](#boolSyntax.mk_select),
[`boolSyntax.dest_select`](#boolSyntax.dest_select)
