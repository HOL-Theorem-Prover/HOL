## `RES_FORALL_SWAP_CONV` {#res_quanLib.RES_FORALL_SWAP_CONV}


```
RES_FORALL_SWAP_CONV : conv
```



Changes the order of two restricted universal quantifications.


When applied to a term of the form `!x::P. !y::Q. R`, the conversion
`RES_FORALL_SWAP_CONV` returns the theorem:
    
       |- (!x::P. !y::Q. R) =  !y::Q. !x::P. R
    
providing that `x` does not occur free in `Q` and `y` does not
occur free in `P`.

### Failure

Fails if applied to a term not of the correct form.

### See also

[`res_quanLib.RES_FORALL_CONV`](#res_quanLib.RES_FORALL_CONV)

