## `MUL_CONV` {#reduceLib.MUL_CONV}


```
MUL_CONV : conv
```



Calculates by inference the product of two numerals.


If `m` and `n` are numerals (e.g. `0`, `1`, `2`, `3`,...), then
`MUL_CONV "m * n"` returns the theorem:
    
       |- m * n = s
    
where `s` is the numeral that denotes the product of the natural
numbers denoted by `m` and `n`.

### Failure

`MUL_CONV tm` fails unless `tm` is of the form  `"m * n"`, where `m` and
`n` are numerals.

### Example

    
    #MUL_CONV "0 * 12";;
    |- 0 * 12 = 0
    
    #MUL_CONV "1 * 1";;
    |- 1 * 1 = 1
    
    #MUL_CONV "6 * 11";;
    |- 6 * 11 = 66
    
