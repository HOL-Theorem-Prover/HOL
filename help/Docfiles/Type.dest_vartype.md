## `dest_vartype`

``` hol4
Type.dest_vartype : hol_type -> string
```

------------------------------------------------------------------------

Breaks a type variable down to its name.

### Failure

Fails with `dest_vartype` if the type is not a type variable.

### Example

``` hol4
- dest_vartype alpha;
> val it = "'a" : string

- try dest_vartype bool;

Exception raised at Type.dest_vartype:
not a type variable
```

### See also

[`Type.mk_vartype`](#Type.mk_vartype),
[`Type.is_vartype`](#Type.is_vartype),
[`Type.dest_type`](#Type.dest_type)
