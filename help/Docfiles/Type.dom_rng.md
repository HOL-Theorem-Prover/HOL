## `dom_rng`

``` hol4
Type.dom_rng : hol_type -> hol_type * hol_type
```

------------------------------------------------------------------------

Breaks a function type into domain and range types.

If `ty` has the form `ty1 -> ty2`, then `dom_rng ty` yields `(ty1,ty2)`.

### Failure

Fails if `ty` is not a function type.

### Example

``` hol4
- dom_rng (bool --> alpha);
> val it = (`:bool`, `:'a`) : hol_type * hol_type

- try dom_rng bool;

Exception raised at Type.dom_rng:
not a function type
```

### See also

[`Type.-->`](#Type..B1KQ4), [`Type.dest_type`](#Type.dest_type),
[`Type.dest_thy_type`](#Type.dest_thy_type)
