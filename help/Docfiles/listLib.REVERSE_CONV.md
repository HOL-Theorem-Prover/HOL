## `REVERSE_CONV` {#listLib.REVERSE_CONV}


```
REVERSE_CONV : conv
```



Computes by inference the result of reversing a list.


`REVERSE_CONV` takes a term `tm` in the following form:
    
       REVERSE [x0;...xn]
    
It returns the theorem
    
       |- REVERSE [x0;...xn] = [xn;...x0]
    
where the right-hand side is the list in the reverse order.

### Failure

`REVERSE_CONV tm` fails if `tm` is not of the form described above.

### Example

Evaluating
    
       REVERSE_CONV “REVERSE [0;1;2;3;4]”;
    
returns the following theorem:
    
       |- REVERSE [0;1;2;3;4] = [4;3;2;1;0]
    

### See also

[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV), [`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV), [`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)

