## `CONJ_DISCHL` {#Drule.CONJ_DISCHL}


```
CONJ_DISCHL : (term list -> thm -> thm)
```



Conjoins multiple assumptions to both sides of an equation.


Given a term list `[t1;...;tn]` and a theorem whose conclusion is an equation
between boolean terms, `CONJ_DISCHL` conjoins all the terms
in the list to both sides of the equation, and removes any of the terms which
were in the assumption list.
    
                            A |- s = t
       --------------------------------------------------------  CONJ_DISCHL
        A - {t1,...,tn} |- (t1/\.../\tn/\s) = (t1/\.../\tn/\t)     [t1,...,tn]
    



### Failure

Fails unless the theorem is an equation, both sides of which, and all the terms
provided, are of type `bool`.

### See also

[`Drule.CONJ_DISCH`](#Drule.CONJ_DISCH)

