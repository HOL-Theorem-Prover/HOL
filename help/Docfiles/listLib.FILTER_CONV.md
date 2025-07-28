## `FILTER_CONV` {#listLib.FILTER_CONV}


```
FILTER_CONV : conv -> conv
```



Computes by inference the result of applying a predicate to the elements of a
list.


`FILTER_CONV` takes a conversion `conv` and a term `tm` in the following form:
    
       FILTER P [x0;...xn]
    
It returns the theorem
    
       |- FILTER P [x0;...xn] = [...xi...]
    
where for every `xi` occurring in the right-hand side of the resulting theorem, `conv “P xi”` returns a theorem `|- P xi = T`.

### Failure

`FILTER_CONV conv tm` fails if `tm` is not of the form described above.

### Example

Evaluating
    
       FILTER_CONV bool_EQ_CONV “FILTER ($= T) [T;F;T]”;
    
returns the following theorem:
    
       |- FILTER($= T)[T;F;T] = [T;T]
    
In general, if the predicate `P` is an explicit lambda abstraction
`(\x. P x)`, the conversion should be in the form
    
       (BETA_CONV THENC conv')
    

### See also

[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV), [`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV), [`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)

