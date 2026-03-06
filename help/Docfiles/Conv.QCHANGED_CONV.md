## `QCHANGED_CONV`

``` hol4
Conv.QCHANGED_CONV : conv -> conv
```

------------------------------------------------------------------------

Makes a conversion fail if applying it raises the `UNCHANGED` exception.

If `c` is a conversion that maps a term `t` to a theorem `|- t = t'`,
then so too is `QCHANGED_CONV c`. If `c` applied to `t` raises the
special `UNCHANGED` exception used by conversions to indicate that they
haven't changed an input, then `QCHANGED_CONV c` will fail, raising a
different exception `HOL_ERR ...` when applied to `t`.

The purpose of this is that some enclosing functions handle the
`UNCHANGED` exception as though `c` had succeeded by returning the
theorem `|- t = t`.

This behaviour is similar to that of `CHANGED_CONV`, except that that
conversion also fails if the conversion `c` returns a theorem when
applied to `t`, and if that theorem has alpha-convertible left and right
hand sides.

### Failure

`QCHANGED_CONV c t` fails (other than by raising `UNCHANGED`) if `c`
applied `t` raises the `UNCHANGED` exception, or if `c` fails otherwise
when applied to `t`.

`QCHANGED_CONV` can be used in places where `CHANGED_CONV` is
appropriate, and where one knows that the conversion argument will not
return an instance of reflexivity, or if one does not mind this
occurring and not being trapped. Because it is no more than an exception
handler, `QCHANGED_CONV` is very efficient.

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED),
[`Conv.CHANGED_CONV`](#Conv.CHANGED_CONV)
