## `mk_type`

``` hol4
Type.mk_type : string * hol_type list -> hol_type
```

------------------------------------------------------------------------

Constructs a compound type.

`mk_type(tyop,[ty1,...,tyn])` returns the HOL type `(ty1,...,tyn)tyop`,
provided `tyop` is the name of a known `n`-ary type constructor.

### Failure

Fails if `tyop` is not the name of a known type, or if `tyop` is known,
but the length of the list of argument types is not equal to the arity
of `tyop`.

### Example

``` hol4
- mk_type ("bool",[]);
> val it = `:bool` : hol_type

- mk_type ("fun",[alpha,it]);
> val it = `:'a -> bool` : hol_type
```

### Comments

Note that type operators with the same name (and arity) may be declared
in different theories. If two theories having type operators with the
same name `s` are in the ancestry of the current theory, then
`mk_type(s,tyl)` will issue a warning before arbitrarily selecting which
type operator to use. In such situations, it is preferable to use
`mk_thy_type` since it allows one to specify exactly which type operator
to use.

### See also

[`Type.mk_thy_type`](#Type.mk_thy_type),
[`Type.dest_type`](#Type.dest_type),
[`Type.mk_vartype`](#Type.mk_vartype), [`Type.-->`](#Type..B1KQ4)
