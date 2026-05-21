## `dest_const`

``` hol4
Term.dest_const : term -> string * hol_type
```

------------------------------------------------------------------------

Breaks apart a constant into name and type.

`dest_const` is a term destructor for constants. If `M` is a constant
with name `c` and type `ty`, then `dest_const M` returns `(c,ty)`.

### Failure

Fails if `M` is not a constant.

### Comments

In Hol98, constants also carry the theory they are declared in. A more
precise and robust way to analyze a constant is with `dest_thy_const`.

### See also

[`Term.mk_const`](#Term.mk_const),
[`Term.mk_thy_const`](#Term.mk_thy_const),
[`Term.dest_thy_const`](#Term.dest_thy_const),
[`Term.is_const`](#Term.is_const), [`Term.dest_abs`](#Term.dest_abs),
[`Term.dest_comb`](#Term.dest_comb), [`Term.dest_var`](#Term.dest_var)
