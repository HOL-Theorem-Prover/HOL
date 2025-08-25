## `mk_disj`

``` hol4
boolSyntax.mk_disj : term * term -> term
```

------------------------------------------------------------------------

Constructs a disjunction.

If `t1` and `t2` are terms, both of type `bool`, then `mk_disj(t1,t2)`
returns the term `t1 \/ t2`.

### Failure

Fails if `t1` or `t2` does not have type `bool`.

### See also

[`boolSyntax.dest_disj`](#boolSyntax.dest_disj),
[`boolSyntax.is_disj`](#boolSyntax.is_disj),
[`boolSyntax.list_mk_disj`](#boolSyntax.list_mk_disj),
[`boolSyntax.strip_disj`](#boolSyntax.strip_disj)
