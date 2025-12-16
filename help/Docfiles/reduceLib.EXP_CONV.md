## `EXP_CONV`

``` hol4
reduceLib.EXP_CONV : conv
```

------------------------------------------------------------------------

Calculates by inference the result of raising one numeral to the power
of another.

If `m` and `n` are numerals (e.g. `0`, `1`, `2`, `3`,...), then
`EXP_CONV "m EXP n"` returns the theorem:

``` hol4
   |- m EXP n = s
```

where `s` is the numeral that denotes the result of raising the natural
number denoted by `m` to the power of the natural number denoted by `n`.

### Failure

`EXP_CONV tm` fails unless `tm` is of the form `"m EXP n"`, where `m`
and `n` are numerals.

### Example

``` hol4
#EXP_CONV "0 EXP 0";;
|- 0 EXP 0 = 1

#EXP_CONV "15 EXP 0";;
|- 15 EXP 0 = 1

#EXP_CONV "12 EXP 1";;
|- 12 EXP 1 = 12

#EXP_CONV "2 EXP 6";;
|- 2 EXP 6 = 64
```
