## `SCANL_CONV` {#listLib.SCANL_CONV}


```
SCANL_CONV : conv -> conv
```



Computes by inference the result of applying a function to the elements of a list.


`SCANL_CONV` takes a conversion `conv` and a term `tm` in the following form:
    
       SCANL f e0 [x1;...xn]
    
It returns the theorem
    
       |- SCANL f e0 [x1;...xn] = [e0; e1; ...;en]
    
where `ei` is the result of applying the function `f` to
the result of the previous iteration and the current element, i.e.,
`ei = f e(i-1) xi`. The iteration starts from the left-hand side (the
head) of the list.
The user supplied conversion `conv` is used to derive a theorem
    
       |- f e(i-1) xi = ei
    
which is used in the next iteration.

### Failure

`SCANL_CONV conv tm` fails if `tm` is not of the form described above,
or failure occurs when evaluating `conv “f e(i-1) xi”`.

### Example

To sum the elements of a list and save the result at each step, one can use
`SCANL_CONV` with `ADD_CONV` from the library `num_lib`.
    
       - load_library_in_place num_lib;
       - SCANL_CONV Num_lib.ADD_CONV “SCANL $+ 0 [1;2;3]”;
       |- SCANL $+ 0[1;2;3] = [0;1;3;6]
    
In general, if the function `f` is an explicit lambda abstraction
`(\x x'. t[x,x'])`, the conversion should be in the form
    
       ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC conv'))
    
where `conv'` applied to `t[x,x']` returns the theorem
    
       |-t[x,x'] = e''.
    

### See also

[`listLib.SCANR_CONV`](#listLib.SCANR_CONV), [`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV), [`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV), [`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)

