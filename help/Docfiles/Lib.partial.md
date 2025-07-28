## `partial` {#Lib.partial}


```
partial : exn -> ('a -> 'b option) -> 'a -> 'b
```



Converts a total function to a partial function.


In ML, there are two main ways for a function to signal that it has been
called on an element outside of its intended domain of application:
exceptions and options. The function `partial` maps a function returning
an element in an option type to one that may raise an exception. Thus,
if `f x` returns `NONE`, then `partial e f x` results in the exception
`e` being raised. If `f x` returns `SOME y`, then `partial e f x`
returns `y`.

The function `partial` has an inverse `total`. Generally speaking,
`(partial err o total) f` equals `f`, provided that `err` is the only
exception that `f` raises. Similarly, `(total o partial err) f` is equal
to `f`.

### Failure

When application of the second argument to the third argument returns `NONE`.

### Example

    
    - Int.fromString "foo";
    > val it = NONE : int option
    
    - partial (Fail "not convertable") Int.fromString "foo";
    ! Uncaught exception:
    ! Fail  "not convertable"
    
    - (total o partial (Fail "not convertable")) Int.fromString "foo";
    > val it = NONE : int option
    



### See also

[`Lib.total`](#Lib.total)

