## `mk_exists1`

``` hol4
boolSyntax.mk_exists1 : term * term -> term
```

------------------------------------------------------------------------

Term constructor for unique existence.

If `v` is a variable and `t` is a term of type `bool`, then
`mk_exists1 (v,t)` returns the term `?!v. t`.

### Failure

Fails if `v` is not a variable or if `t` is not of type `bool`.

### See also

[`boolSyntax.dest_exists1`](#boolSyntax.dest_exists1),
[`boolSyntax.is_exists1`](#boolSyntax.is_exists1)
