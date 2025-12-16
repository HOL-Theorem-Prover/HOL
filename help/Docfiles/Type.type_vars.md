## `type_vars`

``` hol4
Type.type_vars : hol_type -> hol_type list
```

------------------------------------------------------------------------

Returns the set of type variables in a type.

An invocation `type_vars ty` returns a list representing the set of type
variables occurring in `ty`.

### Failure

Never fails.

### Example

``` hol4
- type_vars ((alpha --> beta) --> bool --> beta);
> val it = [`:'a`, `:'b`] : hol_type list
```

### Comments

Code should not depend on how elements are arranged in the result of
`type_vars`.

### See also

[`Type.type_varsl`](#Type.type_varsl),
[`Type.type_var_in`](#Type.type_var_in),
[`Type.exists_tyvar`](#Type.exists_tyvar),
[`Type.polymorphic`](#Type.polymorphic),
[`Term.free_vars`](#Term.free_vars)
