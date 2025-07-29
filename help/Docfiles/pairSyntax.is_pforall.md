## `is_pforall`

``` hol4
pairSyntax.is_pforall : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is a paired universal quantification.

`is_pforall "!pair. t"` returns `true`. If the term is not a paired
universal quantification the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.is_forall`](#boolSyntax.is_forall),
[`pairSyntax.dest_pforall`](#pairSyntax.dest_pforall)
