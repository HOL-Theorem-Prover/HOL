## `mk_var`

``` hol4
Term.mk_var : string * hol_type -> term
```

------------------------------------------------------------------------

Constructs a variable of given name and type.

If `v` is a string and `ty` is a HOL type, then `mk_var(v, ty)` returns
a HOL variable.

### Failure

Never fails.

### Comments

`mk_var` can be used to construct variables with names which are not
acceptable to the term parser. In particular, a variable with the name
of a known constant can be constructed using `mk_var`.

### See also

[`Term.dest_var`](#Term.dest_var), [`Term.is_var`](#Term.is_var),
[`Term.mk_const`](#Term.mk_const), [`Term.mk_comb`](#Term.mk_comb),
[`Term.mk_abs`](#Term.mk_abs)
