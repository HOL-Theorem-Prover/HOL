## `COMB_CONV`

``` hol4
Conv.COMB_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to both immediate sub-terms of an application.

If `t` is an application term of the form `f x`, and `c` is a
conversion, such that `c` maps `f` to `|- f = f'` and `x` to
`|- x = x'`, then `COMB_CONV c` maps `t` to `|- f x = f' x'`.

If one of the two sub-calls raises the `UNCHANGED` exception, then the
result of that call is taken to be the reflexive theorem (`|- x = x` if
`c x` raises the exception, for example). If both conversions raise the
`UNCHANGED` exception, then so too does `COMB_CONV c t`.

### Failure

`COMB_CONV c t` fails if `t` is not an application term, or if `c` fails
when applied to the rator and rand of `t`, or if `c` is not in fact a
conversion (i.e., a function which maps terms `t` to a theorem
`|- t = t'`).

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV),
[`Conv.COMB2_CONV`](#Conv.COMB2_CONV), [`Conv.SUB_CONV`](#Conv.SUB_CONV)
