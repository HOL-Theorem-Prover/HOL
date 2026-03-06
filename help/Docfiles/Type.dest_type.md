## `dest_type`

``` hol4
Type.dest_type : hol_type -> string * hol_type list
```

------------------------------------------------------------------------

Breaks apart a non-variable type.

If `ty` is a type constant, then `dest_type ty` returns `(ty,[])`. If
`ty` is a compound type `(ty1,...,tyn)tyop`, then `dest_type ty` returns
`(tyop,[ty1,...,tyn])`.

### Failure

Fails if `ty` is a type variable.

### Example

``` hol4
- dest_type bool;
> val it = ("bool", []) : string * hol_type list

- dest_type (alpha --> bool);
> val it = ("fun", [`:'a`, `:bool`]) : string * hol_type list
```

### Comments

A more precise alternative is `dest_thy_type`, which tells which theory
the type operator was declared in.

### See also

[`Type.mk_type`](#Type.mk_type),
[`Type.dest_thy_type`](#Type.dest_thy_type),
[`Type.dest_vartype`](#Type.dest_vartype)
