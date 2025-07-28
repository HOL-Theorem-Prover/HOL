## `FOLDR_CONV` {#listLib.FOLDR_CONV}


```
FOLDR_CONV : conv -> conv
```



Computes by inference the result of applying a function to the elements of a
list.


`FOLDR_CONV` takes a conversion `conv` and a term `tm` in the following form:
    
       FOLDR f e [x0;...xn]
    
It returns the theorem
    
       |- FOLDR f e [x0;...xn] = tm'
    
where `tm'` is the result of applying the function `f` iteratively to
the successive elements of the list and the result of the previous
application starting from the tail end of the list. During each
iteration, an expression `f xi ei` is evaluated. The user supplied
conversion `conv` is used to derive a theorem
    
       |- f xi ei = e(i+1)
    
which is used in the next iteration.

### Failure

`FOLDR_CONV conv tm` fails if `tm` is not of the form described above.

### Example

To sum the elements of a list, one can use
`FOLDR_CONV` with `REDUCE_CONV` from the library `numLib`.
    
       - FOLDR_CONV numLib.REDUCE_CONV ``FOLDR $+ 0 [0;1;2;3]``;
       val it = |- FOLDR $+ 0[0;1;2;3] = 6 : thm
    
In general, if the function `f` is an explicit lambda abstraction
`(\x x'. t[x,x'])`, the conversion should be in the form
    
       ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC conv'))
    
where `conv'` applied to `t[x,x']` returns the theorem
    
       |-t[x,x'] = e''.
    

### See also

[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV), [`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)

