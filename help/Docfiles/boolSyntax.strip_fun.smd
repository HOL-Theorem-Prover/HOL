## `strip_fun`

``` hol4
boolSyntax.strip_fun : hol_type -> hol_type list * hol_type
```

------------------------------------------------------------------------

Iteratively breaks apart function types.

If `fty` is of the form `ty1 -> (... (tyn -> ty) ...)`, then
`strip_fun fty` returns `([ty1,...,tyn],ty)`. Note that

``` hol4
   strip_fun(list_mk_fun([ty1,...,tyn],ty))
```

will not return `([ty1,...,tyn],ty)` if `ty` is a function type.

### Failure

Never fails.

### Example

``` hol4
- strip_fun (Type `:(a -> 'bool) -> ('b -> 'c)`);
> val it = ([`:a -> 'bool`, `:'b`], `:'c`) : hol_type list * hol_type
```

### See also

[`boolSyntax.list_mk_fun`](#boolSyntax.list_mk_fun),
[`Type.dom_rng`](#Type.dom_rng), [`Type.dest_type`](#Type.dest_type)
