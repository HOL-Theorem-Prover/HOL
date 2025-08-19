## `dest_thy_const`

``` hol4
Term.dest_thy_const : term -> {Thy:string, Name:string, Ty:hol_type}
```

------------------------------------------------------------------------

Breaks apart a constant into name, theory, and type.

`dest_thy_const` is a term destructor for constants. If `M` is a
constant, declared in theory `Thy` with name `Name`, having type `ty`,
then `dest_thy_const M` returns `{Thy, Name, Ty}`, where `Ty` is equal
to `ty`.

### Failure

Fails if `M` is not a constant.

### Comments

A more precise alternative to `dest_const`.

### See also

[`Term.mk_const`](#Term.mk_const),
[`Term.dest_thy_const`](#Term.dest_thy_const),
[`Term.is_const`](#Term.is_const), [`Term.dest_abs`](#Term.dest_abs),
[`Term.dest_comb`](#Term.dest_comb), [`Term.dest_var`](#Term.dest_var)
