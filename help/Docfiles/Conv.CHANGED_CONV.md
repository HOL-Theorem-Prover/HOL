## `CHANGED_CONV`

``` hol4
Conv.CHANGED_CONV : (conv -> conv)
```

------------------------------------------------------------------------

Makes a conversion fail if applying it leaves a term unchanged.

If `c` is a conversion that maps a term ``` ``t`` ``` to a theorem
`|- t = t'`, where `t'` is alpha-equivalent to `t`, or if `c` raises the
`UNCHANGED` exception when applied to ``` ``t`` ```, then
`CHANGED_CONV c` is a conversion that fails when applied to the term
``` ``t`` ```. If `c` maps ``` ``t`` ``` to `|- t = t'`, where `t'` is
not alpha-equivalent to `t`, then `CHANGED_CONV c` also maps
``` ``t`` ``` to `|- t = t'`. That is, `CHANGED_CONV c` is the
conversion that behaves exactly like `c`, except that it fails whenever
the conversion `c` would leave its input term unchanged (up to
alpha-equivalence).

When `CHANGED_CONV c t` fails, it raises an exception `HOL_ERR ...`, not
`UNCHANGED`, since some enclosing functions handle the `UNCHANGED`
exception as though `c` had succeeded by returning the theorem
`|- t = t`.

### Failure

``` CHANGED_CONV c ``t`` ``` fails if `c` maps ``` ``t`` ``` to
`|- t = t'`, where `t'` is alpha-equivalent to `t`, or if `c` raises the
`UNCHANGED` exception when applied to ``` ``t`` ```, or if `c` fails
when applied to ``` ``t`` ```. The function returned by `CHANGED_CONV c`
may also fail if the ML function `c:term->thm` is not, in fact, a
conversion (i.e. a function that maps a term `t` to a theorem
`|- t = t'`).

`CHANGED_CONV` is used to transform a conversion that may leave terms
unchanged, and therefore may cause a nonterminating computation if
repeated, into one that can safely be repeated until application of it
fails to substantially modify its input term.

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED),
[`Conv.QCHANGED_CONV`](#Conv.QCHANGED_CONV)
