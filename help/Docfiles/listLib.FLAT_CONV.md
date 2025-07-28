## `FLAT_CONV` {#listLib.FLAT_CONV}


```
FLAT_CONV : conv
```



Computes by inference the result of flattening a list of lists.


`FLAT_CONV` takes a term `tm` in the following form:
    
       FLAT [[x00;...x0n]; ...; [xm0;...xmn]]
    
It returns the theorem
    
       |- FLAT [[x00;...x0n];...;[xm0;...xmn]] = [x00;...x0n;...;xm0;...xmn]
    



### Failure

`FLAT_CONV tm` fails if `tm` is not of the form described above.

### Example

Evaluating
    
       FLAT_CONV “FLAT [[0;2;4];[0;1;2;3;4]]”;
    
returns the following theorem:
    
       |- FLAT[[0;2;4];[0;1;2;3;4]] = [0;2;4;0;1;2;3;4]
    

### See also

[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV), [`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV), [`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)

