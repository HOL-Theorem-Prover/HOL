## `mk_select`

``` hol4
boolSyntax.mk_select : term * term -> term
```

------------------------------------------------------------------------

Constructs a choice-term.

If `v` is a variable and `t` is a term of type `bool`, then
`mk_select (v,t)` returns `@var. t`.

### Failure

Fails if `v` is not a variable or if `t` is not of type `bool`.

### See also

[`boolSyntax.dest_select`](#boolSyntax.dest_select),
[`boolSyntax.is_select`](#boolSyntax.is_select)
