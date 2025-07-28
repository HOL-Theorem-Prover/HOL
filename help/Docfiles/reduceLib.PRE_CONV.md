## `PRE_CONV` {#reduceLib.PRE_CONV}


```
PRE_CONV : conv
```



Calculates by inference the predecessor of a numeral.


If `n` is a numeral (e.g. `0`, `1`, `2`, `3`,...), then
`PRE_CONV "PRE n"` returns the theorem:
    
       |- PRE n = s
    
where `s` is the numeral that denotes the predecessor of the natural
number denoted by `n`.

### Failure

`PRE_CONV tm` fails unless `tm` is of the form  ``` ``PRE n`` ```, where `n` is
a numeral.

### Example

    
    > PRE_CONV ``PRE 0``;
    val it = |- PRE 0 = 0 : thm
    
    > PRE_CONV ``PRE 1``;
    val it = |- PRE 1 = 0 : thm
    
    > PRE_CONV ``PRE 22``;
    val it = |- PRE 22 = 21 : thm
    
