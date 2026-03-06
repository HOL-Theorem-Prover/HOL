## `tyvar_sequence`

``` hol4
boolLib.tyvar_sequence : int -> hol_type list
```

------------------------------------------------------------------------

Generates a canonical list of distinct type variables.

A call to `tyvar_sequence n` generates a list consisting of `n` distinct
type variables, with early members of the sequence being `:'a`
("alpha"), `:'b` ("beta") etc. After the first 26 members of the list,
the remainder are of the form `:'a1`, `:'a2` etc.

### Failure

Never fails. If `n` is negative the generated list is empty.

### Example

``` hol4
> tyvar_sequence 3;
val it = [“:α”, “:β”, “:γ”] : hol_type list
```

### See also

[`Type.mk_vartype`](#Type.mk_vartype)
