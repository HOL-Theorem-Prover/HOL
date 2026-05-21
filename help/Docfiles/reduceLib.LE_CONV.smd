## `LE_CONV`

``` hol4
reduceLib.LE_CONV : conv
```

------------------------------------------------------------------------

Proves result of less-than-or-equal-to ordering on two numerals.

If `m` and `n` are both numerals (e.g. `0`, `1`, `2`, `3`,...), then
`LE_CONV "m <= n"` returns the theorem:

``` hol4
   |- (m <= n) = T
```

if the natural number denoted by `m` is less than or equal to that
denoted by `n`, or

``` hol4
   |- (m <= n) = F
```

otherwise.

### Failure

`LE_CONV tm` fails unless `tm` is of the form `"m <= n"`, where `m` and
`n` are numerals.

### Example

``` hol4
#LE_CONV "12 <= 198";;
|- 12 <= 198 = T

#LE_CONV "46 <= 46";;
|- 46 <= 46 = T

#LE_CONV "13 <= 12";;
|- 13 <= 12 = F
```
