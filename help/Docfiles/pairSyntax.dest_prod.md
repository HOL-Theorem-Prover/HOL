## `dest_prod`

``` hol4
pairSyntax.dest_prod : hol_type -> hol_type * hol_type
```

------------------------------------------------------------------------

Breaks a product type into its two component types.

`dest_prod` is a type destructor for products: `dest_pair ":t1#t2"`
returns `(":t1",":t2")`.

### Failure

Fails with `dest_prod` if the argument is not a product type.

### See also

[`pairSyntax.is_prod`](#pairSyntax.is_prod),
[`pairSyntax.mk_prod`](#pairSyntax.mk_prod)
