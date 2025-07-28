## `AND_CONV` {#reduceLib.AND_CONV}


```
AND_CONV : conv
```



Simplifies certain boolean conjunction expressions.


If `tm` corresponds to one of the forms given below, where `t` is an arbitrary
term of type `bool`, then `AND_CONV tm` returns the corresponding theorem. Note
that in the last case the conjuncts need only be alpha-equivalent rather than
strictly identical.
    
       AND_CONV "T /\ t" = |- T /\ t = t
       AND_CONV "t /\ T" = |- t /\ T = t
       AND_CONV "F /\ t" = |- F /\ t = F
       AND_CONV "t /\ F" = |- t /\ F = F
       AND_CONV "t /\ t" = |- t /\ t = t
    

### Failure

`AND_CONV tm` fails unless `tm` has one of the forms indicated above.

### Example

    
    #AND_CONV "(x = T) /\ F";;
    |- (x = T) /\ F = F
    
    #AND_CONV "T /\ (x = T)";;
    |- T /\ (x = T) = (x = T)
    
    #AND_CONV "(?x. x=T) /\ (?y. y=T)";;
    |- (?x. x = T) /\ (?y. y = T) = (?x. x = T)
    
