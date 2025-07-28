## `IMP_RES_FORALL_CONV` {#res_quanLib.IMP_RES_FORALL_CONV}


```
IMP_RES_FORALL_CONV : conv
```



Converts an implication to a restricted universal quantification.


When applied to a term of the form `!x. x IN P ==> Q`, the conversion
`IMP_RES_FORALL_CONV` returns the theorem:
    
       |- (!x. x IN P ==> Q) = !x::P. Q
    

### Failure

Fails if applied to a term not of the form `!x. x IN P ==> Q`.

### See also

[`res_quanLib.RES_FORALL_CONV`](#res_quanLib.RES_FORALL_CONV)

