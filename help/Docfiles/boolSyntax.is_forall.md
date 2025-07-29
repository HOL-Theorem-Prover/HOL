## `is_forall`

``` hol4
boolSyntax.is_forall : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a universal quantification.

If `M` is a term with the form `!x. t`, then `is_forall M` returns
`true`. If `M` is not a universal quantification the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_forall`](#boolSyntax.mk_forall),
[`boolSyntax.dest_forall`](#boolSyntax.dest_forall)
