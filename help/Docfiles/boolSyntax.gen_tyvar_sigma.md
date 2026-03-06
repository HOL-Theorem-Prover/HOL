## `gen_tyvar_sigma`

``` hol4
boolSyntax.gen_tyvar_sigma : hol_type list -> (hol_type,hol_type) Lib.subst
```

------------------------------------------------------------------------

Generates an instantiation mapping each type to a fresh type variable

A call to `gen_tyvar_sigma tys` generates an instantiation (a list of
`{redex,residue}` pairs) mapping the types in `tys` to fresh type
variables (generated in turn with `gen_tyvar`). Standard practice would
be to have `tys` be a list of distinct type variables, but this is not
checked.

### Failure

Never fails.

### Example

``` hol4
> gen_tyvar_sigma [“:'c”, “:'a”, “:'bob”];
val it =
   [{redex = “:γ”, residue = “:%%gen_tyvar%%30”},
    {redex = “:α”, residue = “:%%gen_tyvar%%31”},
    {redex = “:'bob”, residue = “:%%gen_tyvar%%32”}]:
   (hol_type, hol_type) Lib.subst
```

### See also

[`Type.gen_tyvar`](#Type.gen_tyvar),
[`Drule.GEN_TYVARIFY`](#Drule.GEN_TYVARIFY)
