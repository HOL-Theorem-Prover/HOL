## `gen_tyvar`

``` hol4
Type.gen_tyvar : unit -> hol_type
```

------------------------------------------------------------------------

Generate a fresh type variable.

An invocation `gen_tyvar()` generates a type variable `tyv` not seen in
the current session. Furthermore, the concrete syntax of `tyv` is such
that `tyv` is not obtainable by `mk_vartype`, or by parsing.

### Failure

Never fails.

### Example

``` hol4
- gen_tyvar();
> val it = `:%%gen_tyvar%%1` : hol_type

- try Type `:%%gen_tyvar%%1`;

Exception raised at Parse.hol_type parser:
Couldn't make any sense with remaining input of "%%gen_tyvar%%1"

- try mk_vartype "%%gen_tyvar%%1";

Exception raised at Type.mk_vartype:
incorrect syntax
```

### Comments

In general, the actual name returned by `gen_tyvar` should not be relied
on.

Useful for coding some proof procedures.

### See also

[`Term.genvar`](#Term.genvar), [`Term.variant`](#Term.variant)
