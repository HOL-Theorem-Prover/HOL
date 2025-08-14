## `type_var_in`

``` hol4
Type.type_var_in : hol_type -> hol_type -> bool
```

------------------------------------------------------------------------

Checks if a type variable occurs in a type.

An invocation `type_var_in tyv ty` returns `true` if `tyv` occurs in
`ty`. Otherwise, it returns `false`.

### Failure

Fails if `tyv` is not a type variable.

### Example

``` hol4
- type_var_in alpha (bool --> alpha);
> val it = true : bool

- type_var_in alpha bool;
> val it = false : bool
```

### Comments

Can be useful in enforcing side conditions on inference rules.

### See also

[`Type.type_vars`](#Type.type_vars),
[`Type.type_varsl`](#Type.type_varsl),
[`Type.exists_tyvar`](#Type.exists_tyvar)
