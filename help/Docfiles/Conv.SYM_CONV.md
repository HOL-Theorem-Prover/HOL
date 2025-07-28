## `SYM_CONV` {#Conv.SYM_CONV}


```
SYM_CONV : conv
```



Interchanges the left and right-hand sides of an equation.


When applied to an equational term `t1 = t2`, the conversion
`SYM_CONV` returns the theorem:
    
       |- (t1 = t2) = (t2 = t1)
    



### Failure

Fails if applied to a term that is not an equation.

### See also

[`Thm.SYM`](#Thm.SYM)

