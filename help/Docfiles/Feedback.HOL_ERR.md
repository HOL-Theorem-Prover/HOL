## `HOL_ERR` {#Feedback.HOL_ERR}


```
HOL_ERR : {message : string, origin_function : string,
           origin_structure : string} -> exn
```



Standard HOL exception.


`HOL_ERR` is the single exception that HOL functions are expected to raise
when they encounter an anomalous situation.

### Example

Building an application of `HOL_ERR` and binding it to an ML variable
    
       val test_exn =
          HOL_ERR {origin_structure = "Foo",
                   origin_function = "bar",
                   message = "incomprehensible input"};
    

yields
    
       val test_exn = HOL_ERR : exn
    

One can scrutinize the contents of an application of `HOL_ERR` by
pattern matching:
    
       - val HOL_ERR r = test_exn;
    
       > val r = {message = "incomprehensible input",
                  origin_function = "bar",
                  origin_structure = "Foo"}
    

In current ML implementations supporting HOL, exceptions that propagate
to the top level without being handled do not print informatively:
    
       - raise test_exn;
       ! Uncaught exception:
       ! HOL_ERR
    

In such cases, the functions `Raise` and `exn_to_string` can be used
to obtain useful information:
    
       - Raise test_exn;
    
       Exception raised at Foo.bar:
       incomprehensible input
       ! Uncaught exception:
       ! HOL_ERR
    
       - print(exn_to_string test_exn);
    
       Exception raised at Foo.bar:
       incomprehensible input
       > val it = () : unit
    



### See also

[`Feedback`](#Feedback), [`Feedback.error_record`](#Feedback.error_record), [`Feedback.mk_HOL_ERR`](#Feedback.mk_HOL_ERR), [`Feedback.Raise`](#Feedback.Raise), [`Feedback.exn_to_string`](#Feedback.exn_to_string)

