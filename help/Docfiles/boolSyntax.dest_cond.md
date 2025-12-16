## `dest_cond`

``` hol4
boolSyntax.dest_cond : term -> term * term * term
```

------------------------------------------------------------------------

Breaks apart a conditional into the three terms involved.

If `M` has the form `if t then t1 else t2` then `dest_cond M` returns
`(t,t1,t2)`.

### Failure

Fails if `M` is not a conditional.

### See also

[`boolSyntax.mk_cond`](#boolSyntax.mk_cond),
[`boolSyntax.is_cond`](#boolSyntax.is_cond)
