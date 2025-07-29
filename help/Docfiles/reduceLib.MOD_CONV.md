## `MOD_CONV`

``` hol4
reduceLib.MOD_CONV : conv
```

------------------------------------------------------------------------

Calculates by inference the remainder after dividing one numeral by
another.

If `m` and `n` are numerals (e.g. `0`, `1`, `2`, `3`,...), then
`MOD_CONV "m MOD n"` returns the theorem:

``` hol4
   |- m MOD n = s
```

where `s` is the numeral that denotes the remainder after dividing, with
truncation, the natural number denoted by `m` by the natural number
denoted by `n`.

### Failure

`MOD_CONV tm` fails unless `tm` is of the form `"m MOD n"`, where `m`
and `n` are numerals, or if `n` denotes zero.

### Example

``` hol4
#MOD_CONV "0 MOD 0";;
evaluation failed     MOD_CONV

#MOD_CONV "0 MOD 12";;
|- 0 MOD 12 = 0

#MOD_CONV "2 MOD 0";;
evaluation failed     MOD_CONV

#MOD_CONV "144 MOD 12";;
|- 144 MOD 12 = 0

#MOD_CONV "7 MOD 2";;
|- 7 MOD 2 = 1
```
