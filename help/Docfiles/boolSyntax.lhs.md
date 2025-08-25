## `lhs`

``` hol4
boolSyntax.lhs : term -> term
```

------------------------------------------------------------------------

Returns the left-hand side of an equation.

If `M` has the form `t1 = t2` then `lhs M` returns `t1`.

### Failure

Fails if the term is not an equation.

### See also

[`boolSyntax.rhs`](#boolSyntax.rhs),
[`boolSyntax.dest_eq`](#boolSyntax.dest_eq),
[`boolSyntax.mk_eq`](#boolSyntax.mk_eq)
