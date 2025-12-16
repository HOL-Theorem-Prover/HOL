## `is_cond`

``` hol4
boolSyntax.is_cond : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a conditional.

If `M` has the form `if t then t1 else t2` then `is_cond M` returns
`true` If the term is not a conditional the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_cond`](#boolSyntax.mk_cond),
[`boolSyntax.dest_cond`](#boolSyntax.dest_cond)
