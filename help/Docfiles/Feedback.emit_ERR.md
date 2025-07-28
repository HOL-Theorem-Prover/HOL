## `emit_ERR` {#Feedback.emit_ERR}


```
emit_ERR : bool ref
```



Flag controlling output of `HOL_ERR` exceptions.


The boolean flag `emit_ERR` tells whether an application of `HOL_ERR`
should be printed. Its value is consulted by `Raise` when it attempts to
print a textual representation of its argument exception. This flag is
not commonly used, and it may disappear or change in the future.

The default value of `emit_ERR` is `true`.

### Example

    
    - Raise (mk_HOL_ERR "Module" "function" "message");
    
    Exception raised at Module.function:
    message
    ! Uncaught exception:
    ! HOL_ERR
    
    - emit_ERR := false;
    > val it = () : unit
    
    - Raise (mk_HOL_ERR "Module" "function" "message");
    ! Uncaught exception:
    ! HOL_ERR
    



### See also

[`Feedback`](#Feedback), [`Feedback.Raise`](#Feedback.Raise), [`Feedback.emit_MESG`](#Feedback.emit_MESG), [`Feedback.emit_WARNING`](#Feedback.emit_WARNING)

