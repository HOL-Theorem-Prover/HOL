## `DISJ_IMP` {#Drule.DISJ_IMP}


```
DISJ_IMP : (thm -> thm)
```



Converts a disjunctive theorem to an equivalent implicative theorem.


The left disjunct of a disjunctive theorem becomes the negated
antecedent of the newly generated theorem.
    
         A |- t1 \/ t2
       -----------------  DISJ_IMP
        A |- ~t1 ==> t2
    



### Failure

Fails if the theorem is not a disjunction.

### Example

Specializing the built-in theorem `LESS_CASES` gives the theorem:
    
       th = |- m < n \/ n <= m
    
to which `DISJ_IMP` may be applied:
    
       - DISJ_IMP th;
       > val it = |- ~m < n ==> n <= m : thm
    



### See also

[`Thm.DISJ_CASES`](#Thm.DISJ_CASES)

