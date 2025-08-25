## `SUC_CONV`

``` hol4
reduceLib.SUC_CONV : conv
```

------------------------------------------------------------------------

Calculates by inference the successor of a numeral.

If `n` is a numeral (e.g. `0`, `1`, `2`, `3`,...), then
`SUC_CONV "SUC n"` returns the theorem:

``` hol4
   |- SUC n = s
```

where `s` is the numeral that denotes the successor of the natural
number denoted by `n`.

### Failure

`SUC_CONV tm` fails unless `tm` is of the form `"SUC n"`, where `n` is a
numeral.

### Example

``` hol4
#SUC_CONV "SUC 33";;
|- SUC 33 = 34
```
