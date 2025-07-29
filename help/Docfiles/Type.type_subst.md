## `type_subst`

``` hol4
Type.type_subst : (hol_type,hol_type) subst -> hol_type -> hol_type
```

------------------------------------------------------------------------

Instantiates types in a type.

If `theta = [{redex_1,residue_1},...,{redex_n,residue_n}]` is a
`(hol_type,hol_type) subst`, where the `redex_i` are the types to be
substituted for, and the `residue_i` the replacements, and `ty` is a
type to instantiate, the call `type_subst theta ty` will replace each
occurrence of a `redex_i` by the corresponding `residue_i` throughout
`ty`. The replacements will be performed in parallel. If several of the
type instantiations are applicable, the choice is undefined. Each
`redex_i` ought to be a type variable, but if it isn't, it will never be
replaced in `ty`. Also, it is not necessary that any or all of the types
`redex_1...redex_n` should in fact appear in `ty`.

### Failure

Never fails.

### Example

``` hol4
- type_subst [alpha |-> bool] (Type `:'a # 'b`);
> val it = `:bool # 'b` : hol_type

- type_subst [Type`:'a # 'b` |-> Type `:num`, alpha |-> bool]
             (Type`:'a # 'b`);
> val it = `:bool # 'b` : hol_type
```

### See also

[`Term.inst`](#Term.inst), [`Thm.INST_TYPE`](#Thm.INST_TYPE),
[`Lib.|->`](#Lib..GZKQ4), [`Term.subst`](#Term.subst)
