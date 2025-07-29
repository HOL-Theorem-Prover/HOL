## `mk_prod`

``` hol4
pairSyntax.mk_prod : hol_type * hol_type -> hol_type
```

------------------------------------------------------------------------

Constructs a product type from two constituent types.

`mk_prod(ty1, ty2)` returns `ty1 # t2`.

### Failure

Never fails.

### See also

[`pairSyntax.is_prod`](#pairSyntax.is_prod),
[`pairSyntax.dest_prod`](#pairSyntax.dest_prod)
