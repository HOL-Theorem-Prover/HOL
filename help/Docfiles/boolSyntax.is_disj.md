## `is_disj`

``` hol4
boolSyntax.is_disj : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a disjunction.

If `M` has the form `t1 \/ t2`, then `is_disj M` returns `true`. If `M`
is not a disjunction the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_disj`](#boolSyntax.mk_disj),
[`boolSyntax.dest_disj`](#boolSyntax.dest_disj)
