## `mk_eq`

``` hol4
boolSyntax.mk_eq : term * term -> term
```

------------------------------------------------------------------------

Constructs an equation.

`mk_eq(t1, t2)` returns the term `t1 = t2`.

### Failure

Fails if the type of `t1` is not equal to that of `t2`.

### See also

[`boolSyntax.dest_eq`](#boolSyntax.dest_eq),
[`boolSyntax.is_eq`](#boolSyntax.is_eq)
