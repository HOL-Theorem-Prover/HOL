## `is_vartype`

``` hol4
Type.is_vartype : hol_type -> bool
```

------------------------------------------------------------------------

Tests a type to see if it is a type variable.

### Failure

Never fails.

### Example

``` hol4
- is_vartype Type.alpha;
> val it = true : bool

- is_vartype bool;
> val it = false : bool

- is_vartype (Type `:'a  -> bool`);
> val it = false : bool
```

### See also

[`Type.mk_vartype`](#Type.mk_vartype),
[`Type.dest_vartype`](#Type.dest_vartype)
