## `prim_variant`

``` hol4
Term.prim_variant : term list -> term -> term
```

------------------------------------------------------------------------

Rename a variable to be different from any in a list.

The function `prim_variant` is exactly the same as `variant`, except
that it doesn't rename away from constants.

### Failure

`prim_variant l t` fails if any term in the list `l` is not a variable
or if `t` is not a variable.

### Example

``` hol4
- variant [] (mk_var("T",bool));
> val it = `T'` : term

- prim_variant [] (mk_var("T",bool));
> val it = `T` : term
```

### Comments

The extra amount of renaming that `variant` does is useful when
generating new constant names (even though it returns a variable) inside
high-level definition mechanisms. Otherwise, `prim_variant` seems
preferable.

### See also

[`Term.variant`](#Term.variant), [`Term.mk_var`](#Term.mk_var),
[`Term.genvar`](#Term.genvar),
[`Term.mk_primed_var`](#Term.mk_primed_var)
