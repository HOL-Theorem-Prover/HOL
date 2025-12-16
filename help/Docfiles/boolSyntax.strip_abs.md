## `strip_abs`

``` hol4
boolSyntax.strip_abs : term -> term list * term
```

------------------------------------------------------------------------

Iteratively breaks apart abstractions.

If `M` has the form `\x1 ... xn.t` then `strip_abs M` returns
`([x1,...,xn],t)`. Note that

``` hol4
   strip_abs(list_mk_abs([x1,...,xn],t))
```

will not return `([x1,...,xn],t)` if `t` is an abstraction.

### Failure

Never fails.

### See also

[`boolSyntax.list_mk_abs`](#boolSyntax.list_mk_abs),
[`Term.dest_abs`](#Term.dest_abs)
