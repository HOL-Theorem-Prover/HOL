## `prim_mk_const`

``` hol4
Term.prim_mk_const : {Thy:string, Name:string} -> term
```

------------------------------------------------------------------------

Build a constant.

If `Name` is the name of a previously declared constant in theory `Thy`,
then `prim_mk_const {Thy,Name}` will return the specified constant.

### Failure

If `Name` is not the name of a constant declared in theory `Thy`.

### Example

``` hol4
- prim_mk_const {Thy="min", Name="="};
> val it = `$=` : term

- type_of it;
> val it = `:'a -> 'a -> bool` : hol_type
```

### Comments

The difference between `mk_thy_const` (and `mk_const`) and
`prim_mk_const` is that `mk_thy_const` and `mk_const` will create type
instances of polymorphic constants, while `prim_mk_const` merely returns
the originally declared constant.

### See also

[`Term.mk_thy_const`](#Term.mk_thy_const)
