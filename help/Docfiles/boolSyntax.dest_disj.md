## `dest_disj`

``` hol4
boolSyntax.dest_disj : term -> term * term
```

------------------------------------------------------------------------

Term destructor for disjunctions.

If `M` is a term having the form `t1 \/ t2`, then `dest_disj M` returns
`(t1,t2)`.

### Failure

Fails if `M` is not a disjunction.

### See also

[`boolSyntax.mk_disj`](#boolSyntax.mk_disj),
[`boolSyntax.is_disj`](#boolSyntax.is_disj),
[`boolSyntax.strip_disj`](#boolSyntax.strip_disj),
[`boolSyntax.list_mk_disj`](#boolSyntax.list_mk_disj)
