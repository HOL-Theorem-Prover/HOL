## `is_genvar`

``` hol4
Term.is_genvar : term -> bool
```

------------------------------------------------------------------------

Tells if a variable has been built by invoking `genvar`.

`is_genvar v` attempts to tell if `v` has been created by a call to
`genvar`.

### Failure

Never fails.

### Example

``` hol4
- is_genvar (genvar bool);
> val it = true : bool

- is_genvar (mk_var ("%%genvar%%3",bool));
> val it = true : bool
```

### Comments

As the second example shows, it is possible to fool `is_genvar`.
However, it is useful for derived proof tools which use it as part of
their internal operations.

### See also

[`Term.is_var`](#Term.is_var), [`Term.genvar`](#Term.genvar),
[`Type.is_gen_tyvar`](#Type.is_gen_tyvar),
[`Type.gen_tyvar`](#Type.gen_tyvar)
