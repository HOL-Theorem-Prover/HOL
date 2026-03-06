## `is_eq`

``` hol4
boolSyntax.is_eq : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is an equation.

If `M` has the form `t1 = t2` then `is_eq M` returns `true`. If `M` is
not an equation the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_eq`](#boolSyntax.mk_eq),
[`boolSyntax.dest_eq`](#boolSyntax.dest_eq)
