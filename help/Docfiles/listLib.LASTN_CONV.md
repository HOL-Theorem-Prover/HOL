## `LASTN_CONV` {#listLib.LASTN_CONV}


```
LASTN_CONV : conv
```



Computes by inference the result of taking the last n elements of a list.


For any object language list of the form `“[x0;...x(n-k);...;x(n-1)]”` ,
the result of evaluating
    
       LASTN_CONV “LASTN k [x0;...x(n-k);...;x(n-1)]”
    
is the theorem
    
       |- LASTN k [x0;...;x(n-k);...;x(n-1)] = [x(n-k);...;x(n-1)]
    



### Failure

`LASTN_CONV tm` fails if `tm` is not of the form described above,
or `k` is greater than the length of the list.
