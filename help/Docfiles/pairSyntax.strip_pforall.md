## `strip_pforall`

``` hol4
pairSyntax.strip_pforall : term -> term list * term
```

------------------------------------------------------------------------

Iteratively breaks apart paired universal quantifications.

`strip_pforall "!p1 ... pn. t"` returns `([p1,...,pn],t)`. Note that

``` hol4
   strip_pforall(list_mk_pforall([p1,...,pn],t))
```

will not return `([p1,...,pn],t)` if `t` is a paired universal
quantification.

### Failure

Never fails.

### See also

[`boolSyntax.strip_forall`](#boolSyntax.strip_forall),
[`pairSyntax.dest_pforall`](#pairSyntax.dest_pforall)
