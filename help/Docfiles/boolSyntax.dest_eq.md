## `dest_eq`

``` hol4
boolSyntax.dest_eq : term -> term * term
```

------------------------------------------------------------------------

Term destructor for equality.

If `M` is the term `t1 = t2`, then `dest_eq M` returns `(t1, t2)`.

### Failure

Fails if `M` is not an equality.

### See also

[`boolSyntax.mk_eq`](#boolSyntax.mk_eq),
[`boolSyntax.is_eq`](#boolSyntax.is_eq),
[`boolSyntax.lhs`](#boolSyntax.lhs), [`boolSyntax.rhs`](#boolSyntax.rhs)
