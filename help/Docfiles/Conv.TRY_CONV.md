## `TRY_CONV` {#Conv.TRY_CONV}


```
TRY_CONV : conv -> conv
```



Attempts to apply a conversion;
applies identity conversion in case of failure.


`TRY_CONV c t` attempts to apply the conversion `c` to the term `t`;
if this fails, then the identity conversion is applied instead.  That
is, if `c` is a conversion that maps a term `t` to the theorem `|- t = t'`,
then the conversion `TRY_CONV c` also maps `t` to `|- t = t'`. But if `c`
fails when applied to `t`, then `TRY_CONV c t` raises the `UNCHANGED`
exception (which is understood to mean the instance of reflexivity,
`|- t = t`).  If `c` applied to `t` raises the `UNCHANGED` exception,
then so too does `TRY_CONV c t`.

### Failure

Never fails, except that the `UNCHANGED` exception can be raised.

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED), [`Conv.QCHANGED_CONV`](#Conv.QCHANGED_CONV), [`Conv.ALL_CONV`](#Conv.ALL_CONV), [`Conv.QCONV`](#Conv.QCONV)

