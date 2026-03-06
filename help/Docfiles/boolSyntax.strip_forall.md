## `strip_forall`

``` hol4
boolSyntax.strip_forall : term -> term list * term
```

------------------------------------------------------------------------

Iteratively breaks apart universal quantifications.

If `M` has the form `!x1 ... xn. t` then `strip_forall M` returns
`([x1,...,xn],t)`. Note that

``` hol4
   strip_forall(list_mk_forall([x1,...,xn],t,))
```

will not return `([x1,...,xn],t)` if `t` is a universal quantification.

### Failure

Never fails.

### See also

[`boolSyntax.list_mk_forall`](#boolSyntax.list_mk_forall),
[`boolSyntax.dest_forall`](#boolSyntax.dest_forall)
