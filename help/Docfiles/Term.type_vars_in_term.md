## `type_vars_in_term`

``` hol4
Term.type_vars_in_term : term -> hol_type list
```

------------------------------------------------------------------------

Return the type variables occurring in a term.

An invocation `type_vars_in_term M` returns the set of type variables
occurring in `M`.

### Failure

Never fails.

### Example

``` hol4
- type_vars_in_term (concl boolTheory.ONE_ONE_DEF);
> val it = [`:'b`, `:'a`] : hol_type list
```

### See also

[`Term.free_vars`](#Term.free_vars), [`Type.type_vars`](#Type.type_vars)
