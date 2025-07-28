## `LE_CONV` {#reduceLib.LE_CONV}


```
LE_CONV : conv
```



Proves result of less-than-or-equal-to ordering on two numerals.


If `m` and `n` are both numerals (e.g. `0`, `1`, `2`, `3`,...), then
`LE_CONV "m <= n"` returns the theorem:
    
       |- (m <= n) = T
    
if the natural number denoted by `m` is less than or equal to that
denoted by `n`, or
    
       |- (m <= n) = F
    
otherwise.

### Failure

`LE_CONV tm` fails unless `tm` is of the form `"m <= n"`, where `m` and `n`
are numerals.

### Example

    
    #LE_CONV "12 <= 198";;
    |- 12 <= 198 = T
    
    #LE_CONV "46 <= 46";;
    |- 46 <= 46 = T
    
    #LE_CONV "13 <= 12";;
    |- 13 <= 12 = F
    
