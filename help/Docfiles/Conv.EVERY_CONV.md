## `EVERY_CONV`

``` hol4
Conv.EVERY_CONV : (conv list -> conv)
```

------------------------------------------------------------------------

Applies in sequence all the conversions in a given list of conversions.

`EVERY_CONV [c1;...;cn] "t"` returns the result of applying the
conversions `c1`, ..., `cn` in sequence to the term `"t"`. The
conversions are applied in the order in which they are given in the
list. In particular, if `ci "ti"` returns `|- ti=ti+1` for `i` from `1`
to `n`, then `EVERY_CONV [c1;...;cn] "t1"` returns `|- t1=t(n+1)`. If
the supplied list of conversions is empty, then `EVERY_CONV` returns the
identity conversion. That is, `EVERY_CONV [] "t"` raises `UNCHANGED`,
which indicates the result `|- t=t`.

### Failure

`EVERY_CONV [c1;...;cn] "t"` fails if any one of the conversions `c1`,
..., `cn` fails (other than by raising `UNCHANGED`) when applied in
sequence as specified above.

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED), [`Conv.THENC`](#Conv.THENC)
