## `list_mk_abs`

``` hol4
boolSyntax.list_mk_abs : term list * term -> term
```

------------------------------------------------------------------------

Iteratively constructs abstractions.

`list_mk_abs([x1,...,xn],t)` returns the term `\x1 ... xn.t`.

### Failure

Fails if the terms in the list are not variables.

### See also

[`boolSyntax.strip_abs`](#boolSyntax.strip_abs),
[`Term.mk_abs`](#Term.mk_abs)
