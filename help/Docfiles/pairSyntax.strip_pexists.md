## `strip_pexists`

``` hol4
pairSyntax.strip_pexists : term -> term list * term
```

------------------------------------------------------------------------

Iteratively breaks apart paired existential quantifications.

`strip_pexists "?p1 ... pn. t"` returns `([p1,...,pn],t)`. Note that

``` hol4
   strip_pexists(list_mk_pexists([[p1,...,pn],t))
```

will not return `([p1,...,pn],t)` if `t` is a paired existential
quantification.

### Failure

Never fails.

### See also

[`boolSyntax.strip_exists`](#boolSyntax.strip_exists),
[`pairSyntax.dest_pexists`](#pairSyntax.dest_pexists)
