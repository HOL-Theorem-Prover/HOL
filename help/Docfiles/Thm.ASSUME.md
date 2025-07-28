## `ASSUME` {#Thm.ASSUME}


```
ASSUME : term -> thm
```



Introduces an assumption.


When applied to a term `t`, which must have type `bool`, the inference rule
`ASSUME` returns the theorem `t |- t`.
    
       --------  ASSUME t
        t |- t
    



### Failure

Fails unless the term `t` has type `bool`.

### See also

[`Drule.ADD_ASSUM`](#Drule.ADD_ASSUM), [`Thm.REFL`](#Thm.REFL)

