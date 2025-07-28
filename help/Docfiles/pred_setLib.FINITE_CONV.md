## `FINITE_CONV` {#pred_setLib.FINITE_CONV}


```
FINITE_CONV : conv
```



Proves finiteness of sets of the form `{t1;...;tn}`.


The conversion `FINITE_CONV` expects its term argument to be an assertion of
the form `FINITE {t1;...;tn}`. Given such a term, the conversion returns
the theorem
    
       |- FINITE {t1;...;tn} = T
    

### Example

    
    - FINITE_CONV ``FINITE {1;2;3}``;
    > val it = |- FINITE{1;2;3} = T : thm
    
    - FINITE_CONV ``FINITE ({}:num->bool)``;
    > val it = |- FINITE {} = T : thm
    

### Failure

Fails if applied to a term not of the form `FINITE {t1;...;tn}`.
