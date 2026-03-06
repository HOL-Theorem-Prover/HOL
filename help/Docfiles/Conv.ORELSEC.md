## `ORELSEC`

``` hol4
op Conv.ORELSEC : (conv -> conv -> conv)
```

------------------------------------------------------------------------

Applies the first of two conversions that succeeds.

``` (c1 ORELSEC c2) ``t`` ``` returns the result of applying the
conversion `c1` to the term ``` ``t`` ``` if this succeeds. Otherwise
``` (c1 ORELSEC c2) ``t`` ``` returns the result of applying the
conversion `c2` to the term ``` ``t`` ```. If either conversion raises
the `UNCHANGED` exception when applied, this is passed on to `ORELSEC`'s
caller.

### Failure

``` (c1 ORELSEC c2) ``t`` ``` fails if both `c1` and `c2` fail when
applied to ``` ``t`` ```. (This refers to failure other than by raising
`UNCHANGED`).

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED),
[`Conv.FIRST_CONV`](#Conv.FIRST_CONV)
