## `mk_conj`

``` hol4
boolSyntax.mk_conj : term * term -> term
```

------------------------------------------------------------------------

Constructs a conjunction.

`mk_conj(t1, t2)` returns the term `t1 /\ t2`.

### Failure

Fails if `t1` and `t2` do not both have type `bool`.

### See also

[`boolSyntax.dest_conj`](#boolSyntax.dest_conj),
[`boolSyntax.is_conj`](#boolSyntax.is_conj),
[`boolSyntax.list_mk_conj`](#boolSyntax.list_mk_conj),
[`boolSyntax.strip_conj`](#boolSyntax.strip_conj)
