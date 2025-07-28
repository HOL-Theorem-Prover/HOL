## `MK_PAIR` {#PairRules.MK_PAIR}


```
MK_PAIR : thm * thm -> thm
```



Proves equality of pairs constructed from equal components.


When applied to theorems `A1 |- a = x` and `A2 |- b = y`, the inference
rule `MK_PAIR` returns the theorem `A1 u A2 |- (a,b) = (x,y)`.
    
        A1 |- a = x   A2 |- b = y
       ---------------------------  MK_PAIR
        A1 u A2 |- (a,b) = (x,y)
    



### Failure

Fails unless both theorems are equational.
