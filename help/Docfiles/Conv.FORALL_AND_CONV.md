## `FORALL_AND_CONV` {#Conv.FORALL_AND_CONV}


```
FORALL_AND_CONV : conv
```



Moves a universal quantification inwards through a conjunction.


When applied to a term of the form `!x. P /\ Q`, the conversion
`FORALL_AND_CONV` returns the theorem:
    
       |- (!x. P /\ Q) = (!x.P) /\ (!x.Q)
    



### Failure

Fails if applied to a term not of the form `!x. P /\ Q`.

### See also

[`Conv.AND_FORALL_CONV`](#Conv.AND_FORALL_CONV), [`Conv.LEFT_AND_FORALL_CONV`](#Conv.LEFT_AND_FORALL_CONV), [`Conv.RIGHT_AND_FORALL_CONV`](#Conv.RIGHT_AND_FORALL_CONV)

