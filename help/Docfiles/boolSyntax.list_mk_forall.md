## `list_mk_forall`

``` hol4
boolSyntax.list_mk_forall : term list * term -> term
```

------------------------------------------------------------------------

Iteratively constructs a universal quantification.

`list_mk_forall([x1,...,xn],t)` returns `!x1 ... xn. t`.

### Failure

Fails if the terms in the list are not variables or if `t` is not of
type `bool` and the list of terms is non-empty. If the list of terms is
empty the type of `t` can be anything.

### See also

[`boolSyntax.strip_forall`](#boolSyntax.strip_forall),
[`boolSyntax.mk_forall`](#boolSyntax.mk_forall)
