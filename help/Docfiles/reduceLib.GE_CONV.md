## `GE_CONV`

``` hol4
reduceLib.GE_CONV : conv
```

------------------------------------------------------------------------

Proves result of less-than-or-equal-to ordering on two numerals.

If `m` and `n` are both numerals (e.g. `0`, `1`, `2`, `3`,...), then
`GE_CONV "m >= n"` returns the theorem:

``` hol4
   |- (m >= n) = T
```

if the natural number denoted by `m` is greater than or equal to that
denoted by `n`, or

``` hol4
   |- (m >= n) = F
```

otherwise.

### Failure

`GE_CONV tm` fails unless `tm` is of the form `"m >= n"`, where `m` and
`n` are numerals.

### Example

``` hol4
#GE_CONV "15 >= 14";;
|- 15 >= 14 = T

#GE_CONV "100 >= 100";;
|- 100 >= 100 = T

#GE_CONV "0 >= 107";;
|- 0 >= 107 = F
```
