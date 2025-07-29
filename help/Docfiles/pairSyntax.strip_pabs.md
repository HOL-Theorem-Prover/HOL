## `strip_pabs`

``` hol4
pairSyntax.strip_pabs : term -> term list * term
```

------------------------------------------------------------------------

Iteratively breaks apart paired abstractions.

`strip_pabs "\p1 ... pn. t"` returns `([p1,...,pn],t)`. Note that

``` hol4
   strip_pabs(list_mk_abs([p1,...,pn],t))
```

will not return `([p1,...,pn],t)` if `t` is a paired abstraction.

### Failure

Never fails.

### See also

[`boolSyntax.strip_abs`](#boolSyntax.strip_abs),
[`pairSyntax.list_mk_pabs`](#pairSyntax.list_mk_pabs),
[`pairSyntax.dest_pabs`](#pairSyntax.dest_pabs)
