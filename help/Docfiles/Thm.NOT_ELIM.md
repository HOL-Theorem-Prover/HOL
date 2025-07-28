## `NOT_ELIM` {#Thm.NOT_ELIM}


```
NOT_ELIM : thm -> thm
```



Transforms `|- ~t` into `|- t ==> F`.


When applied to a theorem `A |- ~t`, the inference rule `NOT_ELIM` returns the
theorem `A |- t ==> F`.
    
          A |- ~t
       --------------  NOT_ELIM
        A |- t ==> F
    



### Failure

Fails unless the theorem has a negated conclusion.

### See also

[`Drule.IMP_ELIM`](#Drule.IMP_ELIM), [`Thm.NOT_INTRO`](#Thm.NOT_INTRO)

