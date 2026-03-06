## `list_mk_fun`

``` hol4
boolSyntax.list_mk_fun : hol_type list * hol_type -> hol_type
```

------------------------------------------------------------------------

Iteratively constructs function types.

`list_mk_fun([ty1,...,tyn],ty)` returns `ty1 -> ( ... (tyn -> t)...)`.

### Failure

Never fails.

### Example

``` hol4
- list_mk_fun ([alpha,bool],beta);
> val it = `:'a -> bool -> 'b` : hol_type
```

### See also

[`boolSyntax.strip_fun`](#boolSyntax.strip_fun),
[`Type.mk_type`](#Type.mk_type), [`Type.-->`](#Type..B1KQ4)
