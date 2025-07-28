## `EQF_INTRO` {#Drule.EQF_INTRO}


```
EQF_INTRO : (thm -> thm)
```



Converts negation to equality with `F`.


    
         A |- ~tm
       -------------  EQF_INTRO
        A |- tm = F
    



### Failure

Fails if the argument theorem is not a negation.

### See also

[`Drule.EQF_ELIM`](#Drule.EQF_ELIM), [`Drule.EQT_ELIM`](#Drule.EQT_ELIM), [`Drule.EQT_INTRO`](#Drule.EQT_INTRO)

