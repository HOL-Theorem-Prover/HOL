## `dest_select`

``` hol4
boolSyntax.dest_select : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a choice term into selected variable and body.

If `M` has the form `@v. t` then `dest_select M` returns `(v,t)`.

### Failure

Fails if `M` is not an epsilon-term.

### See also

[`boolSyntax.mk_select`](#boolSyntax.mk_select),
[`boolSyntax.is_select`](#boolSyntax.is_select)
