## `NOT_CONV` {#reduceLib.NOT_CONV}


```
NOT_CONV : conv
```



Simplifies certain boolean negation expressions.


If `tm` corresponds to one of the forms given below, where `t` is an arbitrary
term of type `bool`, then `NOT_CONV tm` returns the corresponding theorem.
    
       NOT_CONV "~F"  = |-  ~F = T
       NOT_CONV "~T"  = |-  ~T = F
       NOT_CONV "~~t" = |- ~~t = t
    

### Failure

`NOT_CONV tm` fails unless `tm` has one of the forms indicated above.

### Example

    
    #NOT_CONV "~~~~T";;
    |- ~~~~T = ~~T
    
    #NOT_CONV "~~T";;
    |- ~~T = T
    
    #NOT_CONV "~T";;
    |- ~T = F
    
