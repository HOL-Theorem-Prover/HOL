## `strip_exists`

``` hol4
boolSyntax.strip_exists : term -> term list * term
```

------------------------------------------------------------------------

Iteratively breaks apart existential quantifications.

If `M` has the structure `?x1 ... xn. t` then `strip_exists M` returns
`([x1,...,xn],t)`. Note that

``` hol4
   strip_exists(list_mk_exists(["x1";...;"xn"],"t"))
```

will not return `([x1,...,xn],t)` if `t` is an existential
quantification.

### Failure

Never fails.

### See also

[`boolSyntax.list_mk_exists`](#boolSyntax.list_mk_exists),
[`boolSyntax.dest_exists`](#boolSyntax.dest_exists)
