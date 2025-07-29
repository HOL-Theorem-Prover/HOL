## `FIRST_CONV`

``` hol4
Conv.FIRST_CONV : conv list -> conv
```

------------------------------------------------------------------------

Apply the first of the conversions in a given list that succeeds.

`FIRST_CONV [c1,...,cn] t` returns the result of applying to the term
`t` the first conversion `ci` that succeeds (or raises `UNCHANGED`) when
applied to `t`. The conversions are tried in the order in which they are
given in the list.

### Failure

`FIRST_CONV [c1,...,cn] t` fails if all the conversions `c1`, ..., `cn`
fail when applied to the term `t`. `FIRST_CONV cs t` also fails if `cs`
is the empty list.

### See also

[`Conv.ORELSEC`](#Conv.ORELSEC), [`Conv.UNCHANGED`](#Conv.UNCHANGED)
