## `-->`

``` hol4
op Type.--> : hol_type * hol_type -> hol_type
```

------------------------------------------------------------------------

Right associative infix operator for building a function type.

If `ty1` and `ty2` are HOL types, then `ty1 --> ty2` builds the HOL type
`ty1 -> ty2`.

### Failure

Never fails.

### Example

``` hol4
- bool --> alpha;
> val it = `:bool -> 'a` : hol_type
```

### Comments

This operator associates to the right, that is, `ty1 --> ty2 --> ty3` is
identical to `ty1 --> (ty2 --> ty3)`.

### See also

[`Type.dom_rng`](#Type.dom_rng), [`Type.mk_type`](#Type.mk_type),
[`Type.mk_thy_type`](#Type.mk_thy_type)
