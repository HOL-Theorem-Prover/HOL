## `ERR_to_string`

``` hol4
Feedback.ERR_to_string : (error_record -> string) ref
```

------------------------------------------------------------------------

Alterable function for formatting `HOL_ERR`.

`ERR_to_string` is a reference to a function for formatting the argument
to an application of `HOL_ERR`. It can be used to customize `Raise`.

The default value of `ERR_to_string` is `format_ERR`.

### Example

``` hol4
- fun alt_ERR_report {origin_structure,origin_function,message} =
     String.concat["This just in from ",origin_function, " at ",
                   origin_structure, " : ", message, "\n"];

- ERR_to_string := alt_ERR_report;

- Raise (HOL_ERR {origin_structure = "Foo",
                  origin_function = "bar",
                  message = "incomprehensible input"});

This just in from bar at Foo : incomprehensible input
! Uncaught exception:
! HOL_ERR
```

### See also

[`Feedback`](#Feedback),
[`Feedback.error_record`](#Feedback.error_record),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.Raise`](#Feedback.Raise),
[`Feedback.MESG_to_string`](#Feedback.MESG_to_string),
[`Feedback.WARNING_to_string`](#Feedback.WARNING_to_string)
