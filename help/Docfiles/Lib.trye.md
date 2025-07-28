## `trye` {#Lib.trye}


```
trye : ('a -> 'b) -> 'a -> 'b
```



Maps exceptions into `HOL_ERR`


The standard exception for HOL applications to raise is `HOL_ERR`. The
use of a single exception simplifies the writing of exception handlers
and facilities for decoding and printing error messages. However, ML
functions that raise exceptions, such as `hd` and many others, are often
used to implement HOL programs. In such cases, `trye` may be used to
coerce exceptions into applications of `HOL_ERR`. Note however, that the
`Interrupt` exception is not coerced by `trye`.

The application `trye f x` evaluates `f x`; if this evaluates to `y`,
then `y` is returned. However, if evaluation raises an exception `e`,
there are three cases: if `e` is `Interrupt`, then it is raised; if `e`
is `HOL_ERR`, then it is raised; otherwise, `e` is mapped to an
application of `HOL_ERR` and then raised.

### Failure

Fails if the function application fails.

### Example

    
    - hd [];
    ! Uncaught exception:
    ! Empty
    
    - trye hd [];
    ! Uncaught exception:
    ! HOL_ERR
    
    - trye (fn _ => raise Interrupt) 1;
    > Interrupted
    



### See also

[`Lib`](#Lib), [`Feedback.Raise`](#Feedback.Raise), [`Lib.try`](#Lib.try)

