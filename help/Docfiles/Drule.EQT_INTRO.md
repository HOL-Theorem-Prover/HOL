## `EQT_INTRO` {#Drule.EQT_INTRO}


```
EQT_INTRO : thm -> thm
```



Introduces equality with `T`.


    
          A |- tm
       -------------  EQT_INTRO
        A |- tm = T
    



### Failure

Never fails.

### See also

[`Drule.EQT_ELIM`](#Drule.EQT_ELIM), [`Drule.EQF_ELIM`](#Drule.EQF_ELIM), [`Drule.EQF_INTRO`](#Drule.EQF_INTRO)

