## `ABS` {#Thm.ABS}


```
ABS : term -> thm -> thm
```



Abstracts both sides of an equation.


    
             A |- t1 = t2
       ------------------------  ABS x            [Where x is not free in A]
        A |- (\x.t1) = (\x.t2)
    



### Failure

If the theorem is not an equation, or if the variable `x` is free in the
assumptions `A`.

### Example

    
    > let val m = “m:bool”
      in
          ABS m (REFL m)
      end;
    
    val it = |- (λm. m) = (λm. m) : thm
    

### See also

[`Drule.ETA_CONV`](#Drule.ETA_CONV), [`Drule.EXT`](#Drule.EXT), [`Drule.MK_ABS`](#Drule.MK_ABS)

