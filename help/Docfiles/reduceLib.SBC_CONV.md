## `SBC_CONV` {#reduceLib.SBC_CONV}


```
SBC_CONV : conv
```



Calculates by inference the difference of two numerals.


If `m` and `n` are numerals (e.g. `0`, `1`, `2`, `3`,...), then
`SBC_CONV "m - n"` returns the theorem:
    
       |- m - n = s
    
where `s` is the numeral that denotes the difference of the natural
numbers denoted by `m` and `n`.

### Failure

`SBC_CONV tm` fails unless `tm` is of the form  `"m - n"`, where `m` and
`n` are numerals.

### Example

    
    #SBC_CONV "25 - 30";;
    |- 25 - 30 = 0
    
    #SBC_CONV "200 - 200";;
    |- 200 - 200 = 0
    
    #SBC_CONV "60 - 17";;
    |- 60 - 17 = 43
    
