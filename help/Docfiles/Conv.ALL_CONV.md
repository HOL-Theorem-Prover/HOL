## `ALL_CONV`

``` hol4
Conv.ALL_CONV : conv
```

------------------------------------------------------------------------

Conversion that always raises the `UNCHANGED` exception.

When applied to a term `t`, the conversion `ALL_CONV` raises the special
`UNCHANGED` exception, which indicates to leave `t` unchanged.

### Failure

Always raises the `UNCHANGED` exception.

Identity element for `THENC`.

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED), [`Conv.NO_CONV`](#Conv.NO_CONV),
[`Thm.REFL`](#Thm.REFL)
