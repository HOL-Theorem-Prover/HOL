## `error_record`

``` hol4
Feedback.type error_record = {origin_structure : string,
                     origin_function  : string,
                     message          : string}
```

------------------------------------------------------------------------

Type abbreviation for HOL exceptions in Feedback module.

The type abbreviation `error_record` declares the standard format of HOL
exceptions. The `origin_structure` field denotes the module that the
exception has been raised in, the `origin_function` field gives the name
of the function the exception has been raised in, and the `message`
field should give an explanation of why the exception has been raised.

### See also

[`Feedback`](#Feedback), [`Feedback.HOL_ERR`](#Feedback.HOL_ERR),
[`Feedback.format_ERR`](#Feedback.format_ERR),
[`Feedback.ERR_to_string`](#Feedback.ERR_to_string)
