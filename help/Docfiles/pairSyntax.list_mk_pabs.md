## `list_mk_pabs`

``` hol4
pairSyntax.list_mk_pabs : term list * term -> term
```

------------------------------------------------------------------------

Iteratively constructs paired abstractions.

`list_mk_pabs([p1,...,pn], t)` returns `\p1 ... pn. t`.

### Failure

Fails with `list_mk_pabs` if the terms in the list are not paired
structures of variables.

### See also

[`boolSyntax.list_mk_abs`](#boolSyntax.list_mk_abs),
[`pairSyntax.strip_pabs`](#pairSyntax.strip_pabs),
[`pairSyntax.mk_pabs`](#pairSyntax.mk_pabs)
