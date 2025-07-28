## `EL_CONV` {#listLib.EL_CONV}


```
EL_CONV : conv
```



Computes by inference the result of indexing an element from a list.


For any object language list of the form `“[x0;...xk;...;xn]”` ,
the result of evaluating
    
       EL_CONV “EL k [x0;...xk;...;xn]”
    
is the theorem
    
       |- EL k [x0;...;xk;...;xn] = xk
    



### Failure

`EL_CONV tm` fails if `tm` is not of the form described above,
or `k` is not less than the length of the list.

### See also

[`listLib.ELL_CONV`](#listLib.ELL_CONV)

