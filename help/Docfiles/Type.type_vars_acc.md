## `type_vars_acc`

``` hol4
Type.type_vars_acc : hol_type -> hol_type list -> hol_type list
```

------------------------------------------------------------------------

Returns the set of type variables in a type.

An invocation `type_vars_acc ty A` returns a list representing the
set-theoretic union of the type variables occurring in `ty` and `A`.

### Failure

Never fails.

### Example

``` hol4
- type_vars_acc ((alpha --> beta) --> bool --> beta) [];
> val it = [`:'a`, `:'b`] : hol_type list
```

### Comments

Code should not depend on how elements are arranged in the result of
`type_vars_acc`.

### See also

[`Type.type_vars`](#Type.type_vars),
[`Type.type_varsl`](#Type.type_varsl),
[`Type.type_var_in`](#Type.type_var_in),
[`Type.exists_tyvar`](#Type.exists_tyvar),
[`Type.polymorphic`](#Type.polymorphic),
[`Term.free_vars`](#Term.free_vars)
