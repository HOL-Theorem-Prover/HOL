## `CONJUNCTS` {#Drule.CONJUNCTS}


```
CONJUNCTS : (thm -> thm list)
```



Recursively splits conjunctions into a list of conjuncts.


Flattens out all conjuncts, regardless of grouping. Returns a singleton list
if the input theorem is not a conjunction.
    
           A |- t1 /\ t2 /\ ... /\ tn
       -----------------------------------  CONJUNCTS
        A |- t1   A |- t2   ...   A |- tn
    



### Failure

Never fails.

### Example

Suppose the identifier `th` is bound to the theorem:
    
       A |- (x /\ y) /\ z /\ w
    
Application of `CONJUNCTS` to `th` returns the following list of
theorems:
    
       [A |- x, A |- y, A |- z, A |- w] : thm list
    



### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS), [`Drule.CONJ_LIST`](#Drule.CONJ_LIST), [`Drule.LIST_CONJ`](#Drule.LIST_CONJ), [`Thm.CONJ`](#Thm.CONJ), [`Thm.CONJUNCT1`](#Thm.CONJUNCT1), [`Thm.CONJUNCT2`](#Thm.CONJUNCT2), [`Drule.CONJ_PAIR`](#Drule.CONJ_PAIR)

