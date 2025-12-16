## `list_mk_exists`

``` hol4
boolSyntax.list_mk_exists : term list * term -> term
```

------------------------------------------------------------------------

Iteratively constructs an existential quantification.

`list_mk_exists([x1,...,xn],t)` returns `?x1 ... xn. t`.

### Failure

Fails if the terms in the list are not variables or if `t` is not of
type `bool` and the list of terms is non-empty. If the list of terms is
empty the type of `t` can be anything.

### See also

[`boolSyntax.strip_exists`](#boolSyntax.strip_exists),
[`boolSyntax.mk_exists`](#boolSyntax.mk_exists)
