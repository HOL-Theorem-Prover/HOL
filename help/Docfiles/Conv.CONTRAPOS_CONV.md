## `CONTRAPOS_CONV` {#Conv.CONTRAPOS_CONV}


```
CONTRAPOS_CONV : conv
```



Proves the equivalence of an implication and its contrapositive.


When applied to an implication `P ==> Q`, the conversion `CONTRAPOS_CONV`
returns the theorem:
    
       |- (P ==> Q) = (~Q ==> ~P)
    



### Failure

Fails if applied to a term that is not an implication.

### See also

[`Drule.CONTRAPOS`](#Drule.CONTRAPOS)

