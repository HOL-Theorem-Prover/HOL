## `dest_conj`

``` hol4
boolSyntax.dest_conj : term -> term * term
```

------------------------------------------------------------------------

Term destructor for conjunctions.

If `M` is a term `t1 /\ t2`, then `dest_conj M` returns `(t1,t2)`.

### Failure

Fails if `M` is not a conjunction.

### See also

[`boolSyntax.mk_conj`](#boolSyntax.mk_conj),
[`boolSyntax.is_conj`](#boolSyntax.is_conj),
[`boolSyntax.list_mk_conj`](#boolSyntax.list_mk_conj),
[`boolSyntax.strip_conj`](#boolSyntax.strip_conj)
