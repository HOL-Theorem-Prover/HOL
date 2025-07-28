## `BUTLASTN_CONV` {#listLib.BUTLASTN_CONV}


```
BUTLASTN_CONV : conv
```



Computes by inference the result of dropping the last n elements of a list.


For any object language list of the form `“[x0;...x(n-k);...;x(n-1)]”` ,
the result of evaluating
    
       BUTLASTN_CONV “BUTLASTN k [x0;...x(n-k);...;x(n-1)]”
    
is the theorem
    
       |- BUTLASTN k [x0;...;x(n-k);...;x(n-1)] = [x0;...;x(n-k-1)]
    



### Failure

`BUTLASTN_CONV tm` fails if `tm` is not of the form described above,
or `k` is greater than the length of the list.
