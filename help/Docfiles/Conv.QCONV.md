## `QCONV`

``` hol4
Conv.QCONV : conv -> conv
```

------------------------------------------------------------------------

Stops a conversion raising the `UNCHANGED` exception.

If conversion `c` applied to term `t` raises the `UNCHANGED` exception,
then `QCONV c t` instead returns the theorem `|- t = t`.

### Failure

`QCONV c t` fails if the application of `c` to `t` fails.

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED),
[`Conv.CHANGED_CONV`](#Conv.CHANGED_CONV),
[`Conv.QCHANGED_CONV`](#Conv.QCHANGED_CONV)
