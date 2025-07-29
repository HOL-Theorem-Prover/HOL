## `polymorphic`

``` hol4
Type.polymorphic : hol_type -> bool
```

------------------------------------------------------------------------

Checks if there is a type variable in a type.

An invocation `polymorphic ty` checks to see if `ty` has an occurrence
of any type variable. It is equivalent in functionality to
`not o null o type_vars`, but may be more efficient in some situations,
since it can stop processing once it finds one type variable.

### Failure

Never fails.

### Example

``` hol4
- polymorphic (bool --> alpha --> ind);
> val it = true : bool
```

### Comments

`polymorphic` is also equivalent to `exists_tyvar (K true)`, and no
faster.

### See also

[`Type.type_vars`](#Type.type_vars),
[`Type.type_var_in`](#Type.type_var_in),
[`Type.exists_tyvar`](#Type.exists_tyvar)
