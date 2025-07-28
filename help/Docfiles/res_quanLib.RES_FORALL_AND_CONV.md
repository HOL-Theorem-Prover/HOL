## `RES_FORALL_AND_CONV` {#res_quanLib.RES_FORALL_AND_CONV}


```
RES_FORALL_AND_CONV : conv
```



Splits a restricted universal quantification across a conjunction.


When applied to a term of the form `!x::P. Q /\ R`, the conversion
`RES_FORALL_AND_CONV` returns the theorem:
    
       |- (!x::P. Q /\ R) = ((!x::P. Q) /\ (!x::P. R))
    

### Failure

Fails if applied to a term not of the form `!x::P. Q /\ R`.
