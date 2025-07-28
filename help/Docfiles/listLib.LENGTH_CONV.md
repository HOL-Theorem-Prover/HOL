## `LENGTH_CONV` {#listLib.LENGTH_CONV}


```
LENGTH_CONV : conv
```



Computes by inference the length of an object-language list.


For any object language list of the form `“[x1;x2;...;xn]”`, where `x1`,
`x2`, ..., `xn` are arbitrary terms of the same type, the result of evaluating
    
       LENGTH_CONV “LENGTH [x1;x2;...;xn]”
    
is the theorem
    
       |- LENGTH [x1;x2;...;xn] = n
    
where `n` is the numeral constant that denotes the length of the
list.

### Failure

`LENGTH_CONV tm` fails if `tm` is not of the form `“LENGTH [x1;x2;...;xn]”`
or `“LENGTH []”`.
