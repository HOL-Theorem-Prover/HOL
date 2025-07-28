## `is_gen_tyvar` {#Type.is_gen_tyvar}


```
is_gen_tyvar : hol_type -> bool
```



Checks if a type variable has been created by `gen_tyvar`.

### Failure

Never fails.

### Example

    
    - is_gen_tyvar (gen_tyvar());
    > val it = true : bool
    
    - is_gen_tyvar bool;
    > val it = false : bool
    



### See also

[`Type.gen_tyvar`](#Type.gen_tyvar)

