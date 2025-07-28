## `BUTFIRSTN_CONV` {#listLib.BUTFIRSTN_CONV}


```
BUTFIRSTN_CONV : conv
```



Computes by inference the result of dropping the initial n elements of a list.


For any object language list of the form `“[x0;...x(n-k);...;x(n-1)]”` ,
the result of evaluating
    
       BUTFIRSTN_CONV “BUTFIRSTN k [x0;...x(n-k);...;x(n-1)]”
    
is the theorem
    
       |- BUTFIRSTN k [x0;...;x(n-k);...;x(n-1)] = [x(n-k);...;x(n-1)]
    



### Failure

`BUTFIRSTN_CONV tm` fails if `tm` is not of the form described above,
or `k` is greater than the length of the list.
