## `list_FOLD_CONV` {#listLib.list_FOLD_CONV}


```
list_FOLD_CONV : thm -> conv -> conv
```



Computes by inference the result of applying a function to the elements of a list.


Evaluating `list_FOLD_CONV fthm conv tm` returns a theorem
    
       |- CONST x0' ... xi' ... xn' = tm'
    
The first argument `fthm` should be a theorem of the form
    
      |- !x0 ... xi ... xn. CONST x0 ... xi ... xn = FOLD[LR] f e xi
    
where `FOLD[LR]` means either `FOLDL` or `FOLDR`. The last
argument `tm` is a term of the following form:
    
       CONST x0' ... xi' ... xn'
    
where `xi'` is a concrete list. `list_FOLD_CONV` first
instantiates the input theorem using `tm`. It then calls either
`FOLDL_CONV` or `FOLDR_CONV` with the user supplied conversion `conv`
on the right-hand side.

### Failure

`list_FOLD_CONV fthm conv tm` fails if `fthm` or `tm` is not of the
form described above, or if they do not agree, or the call to
`FOLDL_CONV` OR `FOLDR_CONV` fails.


This function is used to implement conversions for logical constants
which can be expressed in terms of the fold operators. For example,
the constant `SUM` can be expressed in terms of `FOLDR` as in the
following theorem:
    
      |- !l. SUM l = FOLDR $+ 0 l
    
The conversion for `SUM`, `SUM_CONV` can be implemented as
    
       load_library_in_place num_lib;
       val SUM_CONV =
          list_FOLD_CONV (theorem "list" "SUM_FOLDR") Num_lib.ADD_CONV;
    
Then, evaluating `SUM_CONV “SUM [0;1;2;3]”` will return
the following theorem:
    
       |- SUM [0;1;2;3] = 6
    

### See also

[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV), [`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV)

