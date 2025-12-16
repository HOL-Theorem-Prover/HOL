## `NEQ_CONV`

``` hol4
reduceLib.NEQ_CONV : conv
```

------------------------------------------------------------------------

Proves equality or inequality of two numerals.

If `m` and `n` are both numerals (e.g. `0`, `1`, `2`, `3`,...), then
`NEQ_CONV "m = n"` returns the theorem:

``` hol4
   |- (m = n) = T
```

if `m` and `n` are identical, or

``` hol4
   |- (m = n) = F
```

if `m` and `n` are distinct.

### Failure

`NEQ_CONV tm` fails unless `tm` is of the form `"m = n"`, where `m` and
`n` are numerals.

### Example

``` hol4
#NEQ_CONV "12 = 12";;
|- (12 = 12) = T

#NEQ_CONV "14 = 25";;
|- (14 = 25) = F
```
