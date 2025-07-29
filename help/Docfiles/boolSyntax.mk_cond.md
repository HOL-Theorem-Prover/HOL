## `mk_cond`

``` hol4
boolSyntax.mk_cond : term * term * term -> term
```

------------------------------------------------------------------------

Constructs a conditional term.

`mk_cond(t,t1,t2)` constructs an application `COND t t1 t2`. This is
rendered by the prettyprinter as `if t then t1 else t2`.

### Failure

Fails if `t` is not of type `bool` or if `t2` and `t2` are of different
types.

### Comments

The prettyprinter can be trained to print `if t then t1 else t2` as
`t => t1 | t2`.

### See also

[`boolSyntax.dest_cond`](#boolSyntax.dest_cond),
[`boolSyntax.is_cond`](#boolSyntax.is_cond)
