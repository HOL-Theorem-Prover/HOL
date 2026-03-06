## `is_type`

``` hol4
Type.is_type : hol_type -> bool
```

------------------------------------------------------------------------

Tests whether a HOL type is not a type variable.

`is_type ty` returns `true` if `ty` is an application of a type operator
and `false` otherwise.

### Failure

Never fails.

### See also

[`Type.op_arity`](#Type.op_arity), [`Type.mk_type`](#Type.mk_type),
[`Type.mk_thy_type`](#Type.mk_thy_type),
[`Type.dest_type`](#Type.dest_type),
[`Type.dest_thy_type`](#Type.dest_thy_type)
