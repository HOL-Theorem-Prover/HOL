## `is_conj`

``` hol4
boolSyntax.is_conj : term -> bool
```

------------------------------------------------------------------------

Tests a term to see if it is a conjunction.

If `M` has the form `t1 /\ t2`, then `is_conj M` returns `true`. If `M`
is not a conjunction the result is `false`.

### Failure

Never fails.

### See also

[`boolSyntax.mk_conj`](#boolSyntax.mk_conj),
[`boolSyntax.dest_conj`](#boolSyntax.dest_conj)
