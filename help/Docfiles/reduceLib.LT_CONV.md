## `LT_CONV` {#reduceLib.LT_CONV}


```
LT_CONV : conv
```



Proves result of less-than ordering on two numerals.


If `m` and `n` are both numerals (e.g. `0`, `1`, `2`, `3`,...) of type
`:num`, then ``` LT_CONV ``m < n`` ``` returns the theorem:
    
       |- (m < n) = T
    
if the natural number denoted by `m` is less than that denoted by
`n`, or
    
       |- (m < n) = F
    
otherwise.

### Failure

`LT_CONV tm` fails unless `tm` is of the form ``` ``m < n`` ```, where `m` and `n`
are numerals of natural number type (`:num`).

### Example

    
    > LT_CONV ``0 < 12``;
    val it = |- 0 < 12 <=> T : thm
    
    > LT_CONV ``13 < 13``;
    val it = |- 13 < 13 <=> F : thm
    
    > LT_CONV ``25 < 12``;
    val it = |- 25 < 12 <=> F : thm
    

### See also

[`reduceLib.GT_CONV`](#reduceLib.GT_CONV)

