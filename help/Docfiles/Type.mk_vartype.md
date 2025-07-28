## `mk_vartype` {#Type.mk_vartype}


```
mk_vartype : string -> hol_type
```



Constructs a type variable of the given name.

### Failure

Fails if the string does not begin with `'`.

### Example

    
    - mk_vartype "'giraffe";
    > val it = `:'giraffe` : hol_type
    
    - try mk_vartype "test";
    
    Exception raised at Type.mk_vartype:
    incorrect syntax
    



### See also

[`Type.dest_vartype`](#Type.dest_vartype), [`Type.is_vartype`](#Type.is_vartype), [`Type.mk_type`](#Type.mk_type)

