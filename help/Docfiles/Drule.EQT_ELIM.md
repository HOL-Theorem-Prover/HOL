## `EQT_ELIM` {#Drule.EQT_ELIM}


```
EQT_ELIM : (thm -> thm)
```



Eliminates equality with `T`.


    
        A |- tm = T
       -------------  EQT_ELIM
          A |- tm
    



### Failure

Fails if the argument theorem is not of the form `A |- tm = T`.

### See also

[`Drule.EQT_INTRO`](#Drule.EQT_INTRO), [`Drule.EQF_ELIM`](#Drule.EQF_ELIM), [`Drule.EQF_INTRO`](#Drule.EQF_INTRO)

