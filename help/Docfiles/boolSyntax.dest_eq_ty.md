## `dest_eq_ty`

``` hol4
boolSyntax.dest_eq_ty : term -> term * term * hol_type
```

------------------------------------------------------------------------

Term destructor for equality.

If `M` is the term `t1 = t2`, then `dest_eq_ty M` returns
`(t1, t2, ty)`, where `ty` is the type of `t1` (and thus also of `t2`).

### Failure

Fails if `M` is not an equality.

Gives an efficient way to break apart an equality and get the type of
the equality. Useful for obtaining that last fraction of speed when
optimizing the bejeesus out of an inference rule.

### See also

[`boolSyntax.mk_eq`](#boolSyntax.mk_eq),
[`boolSyntax.is_eq`](#boolSyntax.is_eq),
[`boolSyntax.lhs`](#boolSyntax.lhs), [`boolSyntax.rhs`](#boolSyntax.rhs)
