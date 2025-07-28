## `ADD_CONV` {#reduceLib.ADD_CONV}


```
ADD_CONV : conv
```



Calculates by inference the sum of two numerals.


If `m` and `n` are numerals (e.g. `0`, `1`, `2`, `3`,...) of type `:num`, then
``` ADD_CONV ``m + n`` ``` returns the theorem:
    
       |- m + n = s
    
where `s` is the numeral that denotes the sum of the natural
numbers denoted by `m` and `n`.

### Failure

`ADD_CONV tm` fails unless `tm` is of the form  ``` ``m + n`` ```, where `m` and
`n` are numerals of type `:num`.

### Example

    
    > ADD_CONV ``75 + 25``;
    val it = |- 75 + 25 = 100 : thm
    

### See also

[`reduceLib.MUL_CONV`](#reduceLib.MUL_CONV)

