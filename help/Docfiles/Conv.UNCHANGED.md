## `UNCHANGED`

``` hol4
Conv.UNCHANGED : exception
```

------------------------------------------------------------------------

Raised by a conversion to indicate that a term should remain unchanged.

When a conversion `c` is applied to a term `t` this can raise the
exception `UNCHANGED` to indicate that `t` should not be changed to
another term `t'`.

Since in this case we have a function raising an exception, we describe
this as failure of the function `c`. However it may be the intended
result (as used, for example, by `ALL_CONV` or `TRY_CONV`).

When conversions are combined using `THENC` or `ORELSEC`, raising
`UNCHANGED` is treated as though `|- t = t` were returned.

When a conversion `c` is used to produce an inference rule `CONV_RULE c`
or a tactic `CONV_TAC c`, and `c` raises `UNCHANGED`, the rule
`CONV_RULE c` or tactic `CONV_TAC c` succeeds, returning the theorem or
goal unchanged.

### See also

[`Abbrev.conv`](#Abbrev.conv), [`Conv.QCONV`](#Conv.QCONV),
[`Conv.QCHANGED_CONV`](#Conv.QCHANGED_CONV),
[`Conv.ALL_CONV`](#Conv.ALL_CONV), [`Conv.TRY_CONV`](#Conv.TRY_CONV),
[`Conv.CONV_RULE`](#Conv.CONV_RULE),
[`Tactic.CONV_TAC`](#Tactic.CONV_TAC), [`Conv.THENC`](#Conv.THENC),
[`Conv.ORELSEC`](#Conv.ORELSEC)
