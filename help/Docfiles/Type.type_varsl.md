## `type_varsl`

``` hol4
Type.type_varsl : hol_type list -> hol_type list
```

------------------------------------------------------------------------

Returns the set of type variables in a list of types.

An invocation `type_varsl [ty1,...,tyn]` returns a list representing the
set-theoretic union of the type variables occurring in `ty1,...,tyn`.

### Failure

Never fails.

### Example

``` hol4
- type_varsl [alpha, beta, bool, ((alpha --> beta) --> bool --> beta)];
> val it = [`:'a`, `:'b`] : hol_type list
```

### Comments

Code should not depend on how elements are arranged in the result of
`type_varsl`.

### See also

[`Type.type_vars`](#Type.type_vars),
[`Type.type_var_in`](#Type.type_var_in),
[`Type.exists_tyvar`](#Type.exists_tyvar),
[`Type.polymorphic`](#Type.polymorphic),
[`Term.free_vars`](#Term.free_vars)
