## `exists_tyvar`

``` hol4
Type.exists_tyvar : (hol_type -> bool) -> hol_type -> bool
```

------------------------------------------------------------------------

Checks if a type variable satisfying a given condition exists in a type.

An invocation `exists_tyvar P ty` searches `ty` for a type variable
satisfying the predicate `P`. The value `true` is returned if the search
is successful; otherwise `false` is the result.

### Failure

If `P` fails when applied to a type variable encountered in the course
of searching `ty`.

### Example

``` hol4
- exists_tyvar (equal beta) (alpha --> beta --> bool);
> val it = true : bool
```

### Comments

This function is more efficient, in some cases, than
`exists P o type_vars`.
