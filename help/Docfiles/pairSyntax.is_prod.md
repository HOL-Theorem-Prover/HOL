## `is_prod` {#pairSyntax.is_prod}


```
is_prod : hol_type -> bool
```



Tests a type to see if it is a product type.


If `ty` is a type of the form `ty1 # ty2`, then `is_prod ty` returns `true`.

### Failure

Never fails.

### See also

[`pairSyntax.dest_prod`](#pairSyntax.dest_prod), [`pairSyntax.mk_prod`](#pairSyntax.mk_prod)

