## `WARNING_to_string` {#Feedback.WARNING_to_string}


```
WARNING_to_string : (string -> string -> string -> string) ref
```



Alterable function for formatting `HOL_WARNING`.


`WARNING_to_string` is a reference to a function for formatting the argument
to `HOL_WARNING`.

The default value of `WARNING_to_string` is `format_WARNING`.

### Example

    
        - fun alt_WARNING_report s t u =
            String.concat["WARNING---", s,".",t,": ",u,"---END WARNING\n"];
    
        - WARNING_to_string := alt_WARNING_report;
    
        - HOL_WARNING "Foo" "bar" "Look out";
        WARNING---Foo.bar: Look out---END WARNING
        > val it = () : unit
    



### See also

[`Feedback`](#Feedback), [`Feedback.HOL_WARNING`](#Feedback.HOL_WARNING), [`Feedback.format_WARNING`](#Feedback.format_WARNING), [`Feedback.ERR_to_string`](#Feedback.ERR_to_string), [`Feedback.MESG_to_string`](#Feedback.MESG_to_string)

